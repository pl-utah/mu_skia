import argparse
import json
import pathlib
from contextvars import ContextVar
from copy import deepcopy
from dataclasses import dataclass
from typing import Any, Literal, Optional

import numpy as np
import skia  # pyrefly: ignore

from lambda_skia import (
    BlendMode,
    Color,
    Difference,
    Draw,
    Empty,
    Full,
    Geometry,
    ImageRect,
    Intersect,
    Layer,
    LinearGradient,
    Oval,
    Paint,
    Path,
    RadialGradient,
    Rect,
    RRect,
    SaveLayer,
    TextBlob,
    Transform,
    mk_color,
)

warnings_var: ContextVar[list[str]] = ContextVar('warnings', default=[])


def get_reset_warnings():
    warnings = warnings_var.get()
    warnings_var.set([])
    return warnings


def warn(msg):
    warnings = warnings_var.get()
    warnings.append(msg)
    warnings_var.set(warnings)


I = [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0]


def mm(a, b):
    result = [0.0] * 16
    for i in range(4):
        for j in range(4):
            for k in range(4):
                result[i * 4 + j] += a[i * 4 + k] * b[k * 4 + j]
    return result


def radii_to_ltrb(radii: list[list[float]]) -> list[float]:
    return sum(radii, [])


def to_matrix33(matrix: list[float]) -> skia.Matrix:
    """When converting from SkM44 to SkMatrix, the third row and
    column is dropped.  When converting from SkMatrix to SkM44
    the third row and column remain as identity:
    [ a b 0 c ]    [ a b c ]
    [ d e 0 f ] -> [ d e f ]
    [ 0 0 1 0 ]    [ g h i ]
    [ g h 0 i ]
    """

    m33: list[float] = [
        matrix[0],
        matrix[1],
        matrix[3],
        matrix[4],
        matrix[5],
        matrix[7],
        matrix[12],
        matrix[13],
        matrix[15],
    ]

    m33_array = np.array(m33, dtype=np.float32).reshape(3, 3)
    return skia.Matrix(m33_array)


def path_to_rect(skpath: skia.Path) -> Optional[Rect]:
    skrect_post = skia.Rect()
    if not skpath.isRect(skrect_post):
        return None
    return Rect(
        skrect_post.left(),
        skrect_post.top(),
        skrect_post.right(),
        skrect_post.bottom(),
    )


def path_to_image_rect(skpath: skia.Path) -> Optional[ImageRect]:
    skrect_post = skia.Rect()
    if not skpath.isRect(skrect_post):
        return None
    return ImageRect(
        skrect_post.left(),
        skrect_post.top(),
        skrect_post.right(),
        skrect_post.bottom(),
    )


def path_to_rrect(skpath: skia.Path) -> Optional[RRect]:
    skrrect_post = skia.RRect()
    if not skpath.isRRect(skrrect_post):
        return None
    return RRect.from_skrrect(skrrect_post)


def path_to_oval(skpath: skia.Path) -> Optional[Oval]:
    skrect_post = skia.Rect()
    if not skpath.isOval(skrect_post):
        return None
    return Oval(
        skrect_post.left(),
        skrect_post.top(),
        skrect_post.right(),
        skrect_post.bottom(),
    )


type ClipOp = Literal['intersect'] | Literal['difference']


@dataclass
class State:
    clip: Geometry
    transform: list[float]
    layer: Layer
    is_save_layer: bool
    paint: Optional[Paint]  # Only not none, if is_save_layer is True


def compile_skp_to_lskia(commands: list[dict[str, Any]]) -> tuple[Layer, skia.Path]:
    """Compiles serialized Skia commands into λSkia"""
    stack: list[State] = [State(Full(), I, Empty(), False, None)]
    path_map: dict[int, skia.Path] = dict()
    path_index = 0

    def insert_in_path_map(path: skia.Path) -> int:
        nonlocal path_index
        path_map[path_index] = path
        path_index += 1
        return path_index - 1

    for i, command_data in enumerate(commands):

        def compile_paint(json_paint: Optional[dict]) -> Paint:
            warn(f'[INFO] paint: {list(json_paint.keys()) if json_paint else None}')
            if json_paint is None:
                color = Color(1.0, 0.0, 0.0, 0.0)
                blend_mode: BlendMode = '(SrcOver)'
                return Paint(color, blend_mode, '(Solid)', '(IdFilter)', i)
            else:
                for key in json_paint.keys():
                    if key not in (
                        'colorfilter',
                        'shader',
                        'color',
                        'blendMode',
                        'antiAlias',
                        'dither',
                        'strokeWidth',
                        'style',
                        'cap',
                        'strokeJoin',
                        'strokeMiter',
                    ):
                        raise NotImplementedError(key, i)

                color = mk_color(json_paint.get('color', [255, 0, 0, 0]))
                if 'shader' in json_paint.keys():
                    # replace flat color with shader
                    # So the shader is inside SkLocalMatrixShader
                    inner_shader = json_paint['shader']['values']

                    if '01_SkLinearGradient' in inner_shader:
                        is_opaque = all(
                            i[0] == 1 for i in inner_shader['01_SkLinearGradient']['01_colorArray']
                        )
                        color = LinearGradient(is_opaque)
                    elif '01_SkRadialGradient' in inner_shader:
                        is_opaque = all(
                            i[0] == 1 for i in inner_shader['01_SkRadialGradient']['01_colorArray']
                        )
                        color = RadialGradient(is_opaque)
                    else:
                        raise NotImplementedError('unknown shader')

                json_style = json_paint.get('style', 'fill')
                if json_style == 'fill':
                    style = '(Solid)'
                elif json_style == 'stroke':
                    style = '(Stroke)'
                else:
                    raise NotImplementedError(f'Unknown style {json_style}')

                if 'colorfilter' in json_paint:
                    json_color_filter = json_paint['colorfilter']
                    if json_color_filter['name'] == 'SkRuntimeColorFilter':
                        # Runtime effects serialize either their source (old format) or a
                        # Skia-known stable key (current format).  527 is kLuma.
                        values = json_color_filter['values']
                        is_luma = (
                            'sk_luma' in values.get('01_string', '')
                            or values.get('00_int') == 527
                        )
                        assert is_luma
                        color_filter = '(LumaFilter)'
                    else:
                        raise NotImplementedError(f'{json_color_filter["name"]} is not implemented')
                else:
                    color_filter = '(IdFilter)'

                blend_mode = '(' + json_paint.get('blendMode', 'SrcOver') + ')'

                return Paint(color, blend_mode, style, color_filter, i)

        def rectish_contains(inner: Geometry, outer: Geometry) -> bool:
            return (
                isinstance(inner, (Rect, RRect))
                and isinstance(outer, (Rect, RRect))
                and inner.l >= outer.l
                and inner.t >= outer.t
                and inner.r <= outer.r
                and inner.b <= outer.b
            )

        def push_clip(g: Geometry, op: ClipOp):
            # given g and op
            # [..., s(m, c, l, b, p)]
            # -->
            # [..., s(m, op(c, g), l, b, p)]
            if op == 'intersect':
                # skip redundant intersect:
                # [..., s(m, Intersect(Intersect(c, g), g), l, b, p)]
                # -->
                # [..., s(m, Intersect(c, g), l, b, p)]
                current_clip = stack[-1].clip
                if isinstance(current_clip, Intersect):
                    last_clip = current_clip.g2
                    if last_clip == g:
                        return

                    if rectish_contains(last_clip, g):
                        # [..., s(m, Intersect(Intersect(c, a), b), l, b, p)] where a ⊆ b
                        # -->
                        # [..., s(m, Intersect(c, a), l, b, p)]
                        stack[-1].clip = Intersect(current_clip.g1, last_clip)
                        return

                    if rectish_contains(g, last_clip):
                        # [..., s(m, Intersect(Intersect(c, b), a), l, b, p)] where b ⊆ a
                        # -->
                        # [..., s(m, Intersect(c, b), l, b, p)]
                        stack[-1].clip = Intersect(current_clip.g1, g)
                        return
            stack[-1].clip = (Intersect if op == 'intersect' else Difference)(stack[-1].clip, g)

        def push_transform(m: list[float]):
            # given m₂
            # [..., s(m₁, c, l, b, p)]
            # -->
            # [..., s(m₁ × m₂, c, l, b, p)]
            stack[-1].transform = mm(stack[-1].transform, m)

        def identity_transform() -> Transform:
            return Transform(I.copy())

        def mk_draw(g: Geometry):
            p = compile_paint(command_data.get('paint', None))
            # given g and p
            # [..., s(m, c, l, b, p')]
            # -->
            # [..., s(m, c, Draw(l, g, p, c, m), b, p')]
            stack[-1].layer = Draw(
                stack[-1].layer,
                g,
                p,
                stack[-1].clip,
                identity_transform(),
            )

        match command := command_data['command']:
            case 'Save':
                # [..., s₁(m, c, l, b, p)]
                # -->
                # [..., s₁(m, c, l, b, p), s₂(m, c, l, b, p)]
                new_state = deepcopy(stack[-1])
                new_state.is_save_layer = False
                stack.append(new_state)
            case 'SaveLayer':
                # given p₁
                # [..., s₁(m, c, l, b, p₁)]
                # [..., s₁(m, c, l, b, p₁), s₂(m, c, Empty(), b, p₂)]
                new_state = deepcopy(stack[-1])
                new_state.layer = Empty()
                new_state.is_save_layer = True
                new_state.paint = compile_paint(command_data.get('paint', None))
                stack.append(new_state)
            case 'Restore':
                saved_state: State = stack.pop()
                if saved_state.is_save_layer:
                    assert saved_state.paint is not None
                    # [..., s₁(m₁, c₁, l₁, b₁, p₁), s₂(m₂, c₂, l₂, True, p₂)]
                    # -->
                    # [..., s₁(m₁, c₁, SaveLayer(l₁, l₂, p₂), b₁, p₁)]
                    stack[-1].layer = SaveLayer(
                        stack[-1].layer, saved_state.layer, saved_state.paint
                    )
                else:
                    # [..., s₁(m₁, c₁, l₁, b₁, p₁), s₂(m₂, c₂, l₂, True, None)]
                    # -->
                    # [..., s₁(m₁, c₁, l₂, b₁, p₁)]
                    stack[-1].layer = saved_state.layer
            case 'DrawPaint':
                mk_draw(Full())
            case 'DrawTextBlob':
                x = float(command_data['x'])
                y = float(command_data['y'])
                bounds = [float(bound) for bound in command_data['bounds']]
                rect = skia.Rect.MakeLTRB(
                    x + bounds[0],
                    y + bounds[1],
                    x + bounds[2],
                    y + bounds[3],
                )
                skpath = skia.Path.Rect(rect)
                skpath.transform(to_matrix33(stack[-1].transform))
                tight_bounds = skpath.computeTightBounds()
                assert tight_bounds is not None
                left = tight_bounds.left()
                top = tight_bounds.top()
                right = tight_bounds.right()
                bottom = tight_bounds.bottom()
                mk_draw(TextBlob(left, top, 0.0, 0.0, right - left, bottom - top))
            case 'DrawImageRect':
                dst = [float(d) for d in command_data['dst']]
                skrect = skia.Rect.MakeLTRB(*dst)
                skpath = skia.Path.Rect(skrect)
                skpath.transform(to_matrix33(stack[-1].transform))
                image_rect = path_to_image_rect(skpath)
                assert image_rect is not None, 'cant transform image rect'
                mk_draw(image_rect)
            case 'DrawRect':
                coords = [float(coord) for coord in command_data['coords']]
                skrect_pre = skia.Rect.MakeLTRB(*coords)
                skpath = skia.Path.Rect(skrect_pre)
                skpath.transform(to_matrix33(stack[-1].transform))
                rect = path_to_rect(skpath)
                if rect is None:
                    index = insert_in_path_map(skpath)
                    geometry: Geometry = Path(i, index)
                else:
                    geometry = rect
                mk_draw(geometry)
            case 'DrawOval':
                coords = [float(coord) for coord in command_data['coords']]
                skrect_pre = skia.Rect.MakeLTRB(*coords)
                skpath = skia.Path.Oval(skrect_pre)
                skpath.transform(to_matrix33(stack[-1].transform))
                oval = path_to_oval(skpath)
                assert oval is not None, 'cant transform oval'
                mk_draw(oval)
            case 'DrawRRect':
                coords, *radii = command_data['coords']
                ltrb_radii = radii_to_ltrb(radii)
                values = [float(val) for val in coords + ltrb_radii]
                rrect = RRect(*values)
                skrrect = rrect.to_skrrect()
                skpath = skia.Path.RRect(skrrect)
                skpath.transform(to_matrix33(stack[-1].transform))
                rrect_geometry = path_to_rrect(skpath)
                if rrect_geometry is None:
                    index = insert_in_path_map(skpath)
                    geometry = Path(i, index)
                else:
                    geometry = rrect_geometry
                mk_draw(geometry)
            case 'DrawPath':
                skpath = Path.from_jsonpath(command_data['path'])
                skpath.transform(to_matrix33(stack[-1].transform))
                rect = path_to_rect(skpath)
                if rect is None:
                    index = insert_in_path_map(skpath)
                    geometry = Path(i, index)
                else:
                    geometry = rect
                mk_draw(geometry)
            case 'ClipRect':
                coords = [float(coord) for coord in command_data['coords']]
                op: ClipOp = command_data['op']
                skrect_pre = skia.Rect.MakeLTRB(*coords)
                skpath = skia.Path.Rect(skrect_pre)
                skpath.transform(to_matrix33(stack[-1].transform))
                rect = path_to_rect(skpath)
                if rect is None:
                    index = insert_in_path_map(skpath)
                    geometry: Geometry = Path(i, index)
                else:
                    geometry = rect
                push_clip(geometry, op)
            case 'ClipRRect':
                coords, *radii = command_data['coords']
                ltrb_radii = radii_to_ltrb(radii)
                op: ClipOp = command_data['op']
                rrect = RRect(*[float(i) for i in coords + ltrb_radii])
                skrrect_pre = rrect.to_skrrect()
                skpath = skia.Path.RRect(skrrect_pre)
                skpath.transform(to_matrix33(stack[-1].transform))
                rrect_geometry = path_to_rrect(skpath)
                if rrect_geometry is None:
                    index = insert_in_path_map(skpath)
                    geometry = Path(i, index)
                else:
                    geometry = rrect_geometry
                push_clip(geometry, op)
            case 'ClipPath':
                skpath = Path.from_jsonpath(command_data['path'])
                skpath.transform(to_matrix33(stack[-1].transform))
                index = insert_in_path_map(skpath)
                op: ClipOp = command_data['op']
                push_clip(Path(i, index), op)
            case 'Concat44':
                matrix: list[float] = [i for s in command_data['matrix'] for i in s]
                push_transform(matrix)
            case _:
                raise NotImplementedError(command + ' @ ' + str(i))

    assert len(stack) == 1, 'Unbalanced Save/SaveLayer'
    return (stack[-1].layer, path_map)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('input', type=pathlib.Path)
    parser.add_argument('--output', '-o', type=pathlib.Path)

    args = parser.parse_args()

    with args.input.open('rb') as f:
        skp = json.load(f)

    layer, _ = compile_skp_to_lskia(skp['commands'])

    if args.output:
        with args.output.open('w') as f:
            f.write(layer)
    else:
        print('(let test ' + layer.sexp() + ')')
