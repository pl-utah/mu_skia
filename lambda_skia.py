from dataclasses import dataclass, fields
from typing import Any, Literal, Self, assert_never, override

import skia  # pyrefly: ignore


@dataclass
class Node:
    def sexp(self) -> str:
        class_name = self.__class__.__name__

        try:
            field_values = [getattr(self, field.name) for field in fields(self)]

            values: list[str] = []
            for value in field_values:
                match value:
                    case Node():
                        values.append(value.sexp())
                    case str():
                        values.append(value)
                    case bool():
                        values.append('true' if value else 'false')
                    case _:
                        values.append(str(value))

            return f'({class_name} {" ".join(values)})' if values else f'({class_name})'
        except TypeError:
            raise NotImplementedError()


@dataclass
class Color(Node):
    """A solid color defined by alpha, red, green, and blue channel values."""

    a: float
    r: float
    g: float
    b: float

    def pprint(self) -> str:
        return f'Color({int(self.a * 255)}, {int(self.r * 255)}, {int(self.b * 255)}, {int(self.g * 255)})'


@dataclass
class LinearGradient(Node):
    """Linear gradient shader"""

    is_opaque: bool

    def pprint(self) -> str:
        return f'LinearGradient({self.is_opaque})'


@dataclass
class RadialGradient(Node):
    """Radial gradient shader"""

    is_opaque: bool

    def pprint(self) -> str:
        return f'RadialGradient({self.is_opaque})'


@dataclass
class Transform(Node):
    """4x4 transform matrix"""

    matrix: list[float]

    @override
    def sexp(self) -> str:
        return '(Matrix ' + ' '.join([str(i) for i in self.matrix]) + ')'

    def pprint(self) -> str:
        return 'Mat' + str(self.matrix)


def mk_color(argb: list[int]):
    return Color(*[i / 255 for i in argb])


type Fill = Color | LinearGradient | RadialGradient

type BlendMode = Literal['(SrcOver)']

type Style = Literal['(Solid)', '(Stroke)']

type Filter = Literal['(IdFilter)', '(LumaFilter)']


@dataclass
class Geometry(Node):
    def pprint(self) -> str:
        raise NotImplementedError()


@dataclass
class Full(Geometry):
    """A geometry representing the full clip. Used in conjunction with
    DrawPaint"""

    @override
    def pprint(self) -> str:
        return 'Full()'


@dataclass
class Rect(Geometry):
    """A rectangular geometry defined by left, top, right, and bottom
    coordinates."""

    l: float
    t: float
    r: float
    b: float

    @override
    def pprint(self) -> str:
        return f'Rect({self.l}, {self.t}, {self.r}, {self.b})'


@dataclass
class TextBlob(Geometry):
    """A textblob geometry defined by text, position, and attributes"""

    x: float
    y: float
    l: float
    t: float
    r: float
    b: float

    @override
    def pprint(self) -> str:
        return f'TextBlob({self.x}, {self.y}, {self.l}, {self.t}, {self.r}, {self.b})'


@dataclass
class ImageRect(Geometry):
    l: float
    t: float
    r: float
    b: float

    @override
    def pprint(self) -> str:
        return f'ImageRect({self.l}, {self.t}, {self.r}, {self.b})'


@dataclass
class RRect(Geometry):
    """An elliptical rounded rectangular geometry defined by left, top, right,
    and bottom coordinates, and the radii."""

    l: float
    t: float
    r: float
    b: float

    ul_x: float
    ul_y: float

    ur_x: float
    ur_y: float

    lr_x: float
    lr_y: float

    ll_x: float
    ll_y: float

    @override
    def pprint(self) -> str:
        return f'RRect({self.l}, {self.t}, {self.r}, {self.b}, {self.ul_x}, {self.ul_y}, {self.ur_x}, {self.ur_y}, {self.lr_x}, {self.lr_y}, {self.ll_x}, {self.lr_y})'

    def to_skrrect(self) -> skia.RRect:
        rect = skia.Rect.MakeLTRB(self.l, self.t, self.r, self.b)
        rrect = skia.RRect()
        rrect.setRectRadii(
            rect,
            [
                skia.Point(self.ul_x, self.ul_y),
                skia.Point(self.ur_x, self.ur_y),
                skia.Point(self.lr_x, self.lr_y),
                skia.Point(self.ll_x, self.ll_y),
            ],
        )

        return rrect

    @staticmethod
    def from_skrrect(skrrect) -> Self:
        ul = skrrect.radii(skia.RRect.Corner.kUpperLeft_Corner)
        ur = skrrect.radii(skia.RRect.Corner.kUpperRight_Corner)
        lr = skrrect.radii(skia.RRect.Corner.kLowerRight_Corner)
        ll = skrrect.radii(skia.RRect.Corner.kLowerLeft_Corner)
        rect = skrrect.rect()
        return RRect(
            rect.left(),
            rect.top(),
            rect.right(),
            rect.bottom(),
            ul.x(),
            ul.y(),
            ur.x(),
            ur.y(),
            lr.x(),
            lr.y(),
            ll.x(),
            ll.y(),
        )


@dataclass
class Oval(Geometry):
    """A rectangular geometry defined by left, top, right, and bottom
    coordinates."""

    l: float
    t: float
    r: float
    b: float

    @override
    def pprint(self) -> str:
        return f'Oval({self.l}, {self.t}, {self.r}, {self.b})'


@dataclass
class Path(Geometry):
    """A geometry that defines an arbitrary closed or open path"""

    index: int
    index2: int

    @override
    def pprint(self) -> str:
        return f'Path({self.index2})'

    @staticmethod
    def from_jsonpath(path_data: dict[str, Any]) -> skia.Path:
        """Regenerate path from json. This function needs the value under they
        key "path" within the command"""
        fill_type = path_data.get('fillType', 'winding')

        path = skia.Path()
        if fill_type == 'winding':
            path.setFillType(skia.PathFillType.kWinding)
        elif fill_type == 'evenOdd':
            path.setFillType(skia.PathFillType.kEvenOdd)
        elif fill_type == 'inverseWinding':
            path.setFillType(skia.PathFillType.kInverseWinding)
        else:
            raise ValueError(f'Unknown fillType: {fill_type}')

        for verb in path_data['verbs']:
            if isinstance(verb, dict):
                if 'move' in verb:
                    x, y = verb['move']
                    path.moveTo(x, y)
                elif 'cubic' in verb:
                    pts = verb['cubic']
                    (x1, y1), (x2, y2), (x3, y3) = pts
                    path.cubicTo(x1, y1, x2, y2, x3, y3)
                elif 'line' in verb:
                    x, y = verb['line']
                    path.lineTo(x, y)
                elif 'quad' in verb:
                    pts = verb['quad']
                    (x1, y1), (x2, y2) = pts
                    path.quadTo(x1, y1, x2, y2)
                elif 'conic' in verb:
                    pts = verb['conic']
                    (x1, y1), (x2, y2), w = pts
                    path.conicTo(x1, y1, x2, y2, w)
                else:
                    raise ValueError(f'Unknown verb key: {verb}')
            elif isinstance(verb, str):
                if verb == 'close':
                    path.close()
                else:
                    raise ValueError(f'Unknown verb string: {verb}')
            else:
                raise TypeError(f'Unexpected verb type: {verb}')

        return path


@dataclass
class Intersect(Geometry):
    """A geometry that represents the intersection of two or more geometries."""

    g1: Geometry
    g2: Geometry

    @override
    def pprint(self) -> str:
        return self.g1.pprint() + ' ∩ ' + self.g2.pprint()


@dataclass
class Difference(Geometry):
    """A geometry that represents the difference of two or more geometries."""

    g1: Geometry
    g2: Geometry

    @override
    def pprint(self) -> str:
        return self.g1.pprint() + ' / ' + self.g2.pprint()


@dataclass
class Paint(Node):
    """Configuration that determines how geometries are filled and blended when
    drawn."""

    fill: Fill
    blend_mode: BlendMode
    style: Style
    color_filter: Filter
    index: int  # This points to the skia command that uses this paint in the skp

    def pprint(self) -> str:
        return (
            'Paint('
            + self.fill.pprint()
            + ', '
            + self.blend_mode
            + ', '
            + self.style
            + ', '
            + self.color_filter
            + ')'
        )


class Layer(Node):
    """A drawing surface that can contain pixels and be composited with other
    layers."""

    def pretty_print(self, indent_level: int = 0) -> list[tuple[int, str]]:
        """Pretty-printing a layer, returns a list of tuples of an int and a
        string. Each element is a line, the string tis content and the integer
        tells us how nested it is"""
        raise NotImplementedError()


@dataclass
class Empty(Layer):
    """A layer that contains no pixels and serves as the base for all drawing
    operations."""

    @override
    def pretty_print(self, indent_level=0) -> list[tuple[int, str]]:
        return [(indent_level, 'Empty()')]


@dataclass
class SaveLayer(Layer):
    """A layer that composites a top layer onto a bottom layer using the
    specified paint settings."""

    bottom: Layer
    top: Layer
    paint: Paint

    @override
    def pretty_print(self, indent_level: int = 0) -> list[tuple[int, str]]:
        # i, self.bottom
        # i, SaveLayer self.paint
        # i + 1 self.top
        res: list[tuple[int, str]] = []
        if not isinstance(self.bottom, Empty):
            res = self.bottom.pretty_print(indent_level)

        res.append((indent_level, 'SaveLayer ' + self.paint.pprint() + ':'))
        if isinstance(self.top, Empty):
            res.append((indent_level + 1, 'Empty()'))
        else:
            res.extend(self.top.pretty_print(indent_level + 1))
        return res


@dataclass
class Clip(Layer):
    layer: Layer
    clip: Geometry
    transform: Transform

    @override
    def pretty_print(self, indent_level: int = 0) -> list[tuple[int, str]]:
        # i, Clip with self.clip
        # i + 1, self.layer

        res: list[tuple[int, str]] = []
        res.append((indent_level, 'Clip with ' + self.clip.pprint() + ':'))
        res.append((indent_level + 1, '@ ' + self.transform.pprint()))
        if isinstance(self.layer, Empty):
            res.append((indent_level + 1, 'Empty()'))
        else:
            res.extend(self.layer.pretty_print(indent_level + 1))
        return res


@dataclass
class Draw(Layer):
    """A layer that renders a geometry onto an existing layer with the given
    paint and clipping region."""

    bottom: Layer
    shape: Geometry
    paint: Paint
    clip: Geometry
    transform: Transform

    @override
    def pretty_print(self, indent_level: int = 0) -> list[tuple[int, str]]:
        # i, self.bottom
        # i, Draw()
        res: list[tuple[int, str]] = []
        if not isinstance(self.bottom, Empty):
            res = self.bottom.pretty_print(indent_level)

        res.append((indent_level, 'Draw ' + self.shape.pprint()))
        res.append((indent_level + 1, 'with ' + self.paint.pprint()))
        res.append((indent_level + 1, 'in ' + self.clip.pprint()))
        res.append((indent_level + 1, '@ ' + self.transform.pprint()))
        return res


def pretty_print_layer(layer: Layer) -> str:
    output = layer.pretty_print()
    res = ''
    for i, line in output:
        res += '  ' * i + line + '\n'

    return res


def paint_to_lean(paint: Paint, is_savelayer=False) -> str:
    fill = ''

    if is_savelayer:
        match paint.fill:
            case Color(a, _, _, _):
                fill = f'Fill.pixel (Alpha {1 if a == 1.0 else a})'
            case _:
                fill = f'Fill.pixel (Alpha 1)'
    else:
        match paint.fill:
            case Color(a, r, g, b):
                fill = (
                    f'Fill.pixel ⟨{1 if a == 1.0 else a}, {r * a}, {g * a}, {b * a}, by norm_num⟩'
                )
            case LinearGradient(is_opaque):
                fill = f"Fill.shader (LinearGradient {'true' if is_opaque else 'false'})"
            case RadialGradient(is_opaque):
                fill = f"Fill.shader (RadialGradient {'true' if is_opaque else 'false'})"

    blend_mode = 'BlendMode.' + paint.blend_mode[1:-1].lower()
    style = paint.style[1:-1].lower()
    if style == 'solid':
        style = 'id'
    color_filter_name = paint.color_filter[1:-1].lower()
    if color_filter_name == 'idfilter':
        color_filter = 'Filter.id'
    elif color_filter_name == 'lumafilter':
        color_filter = 'Filter.custom LumaFilter'
    else:
        color_filter = 'Filter.' + color_filter_name

    return f'({fill}, {blend_mode}, {style}, {color_filter})'


def _lean_num(x: float) -> str:
    s = str(x)
    # Prevent Lean from parsing e.g. `Rect 0.0 -388.0 ...` as subtraction.
    return f'({s})' if s.startswith('-') else s


def shape_to_lean(shape: Geometry) -> str:
    match shape:
        case Rect(l, t, r, b):
            return f'(Rect {_lean_num(l)} {_lean_num(t)} {_lean_num(r)} {_lean_num(b)})'
        case Full():
            return 'Full'
        case Intersect(a, b):
            return f'(intersect {shape_to_lean(a)} {shape_to_lean(b)})'
        case Difference(a, b):
            return f'(difference {shape_to_lean(a)} {shape_to_lean(b)})'
        case RRect(a, b, c, d, e, f, g, h):
            return f'(RRect {_lean_num(a)} {_lean_num(b)} {_lean_num(c)} {_lean_num(d)} {_lean_num(e)} {_lean_num(f)} {_lean_num(g)} {_lean_num(h)})'
        case Oval(l, t, r, b):
            return f'(Oval {_lean_num(l)} {_lean_num(t)} {_lean_num(r)} {_lean_num(b)})'
        case Path(a, b):
            return f'(Path {_lean_num(b)})'
        case TextBlob(a, b, c, d, e, f):
            return f'(TextBlob {_lean_num(a)} {_lean_num(b)} {_lean_num(c)} {_lean_num(d)} {_lean_num(e)} {_lean_num(f)})'
        case ImageRect(l, t, r, b):
            return f'(ImageRect {_lean_num(l)} {_lean_num(t)} {_lean_num(r)} {_lean_num(b)})'
        case _:
            raise NotImplementedError(str(shape))


def layer_to_lean(layer: Layer) -> str:
    match layer:
        case Empty():
            return 'empty'
        case SaveLayer(bottom, top, paint):
            return ' '.join(
                [
                    '(saveLayer',
                    layer_to_lean(bottom),
                    layer_to_lean(top),
                    paint_to_lean(paint, is_savelayer=True),
                    ')',
                ]
            )
        case Draw(bottom, shape, paint, clip, transform):
            return ' '.join(
                [
                    '(draw',
                    layer_to_lean(bottom),
                    shape_to_lean(shape),
                    paint_to_lean(paint),
                    shape_to_lean(clip),
                    ')',
                ]
            )
        case _:
            raise AssertionError('unreachable code')
