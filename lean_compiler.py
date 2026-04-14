import argparse
import json
import pathlib

from lambda_skia import (
    Difference,
    Draw,
    Empty,
    Intersect,
    SaveLayer,
    layer_to_lean,
)
from lambda_skia import (
    Path as LPath,
)
from skp_compiler import compile_skp_to_lskia


def remap_geometry_paths(geometry, local_to_global: dict[int, int]):
    match geometry:
        case LPath(i, index2):
            return LPath(i, local_to_global[index2])
        case Intersect(g1, g2):
            return Intersect(
                remap_geometry_paths(g1, local_to_global),
                remap_geometry_paths(g2, local_to_global),
            )
        case Difference(g1, g2):
            return Difference(
                remap_geometry_paths(g1, local_to_global),
                remap_geometry_paths(g2, local_to_global),
            )
        case _:
            return geometry


def remap_layer_paths(layer, local_to_global: dict[int, int]):
    match layer:
        case Empty():
            return layer
        case Draw(bottom, shape, paint, clip, transform):
            return Draw(
                remap_layer_paths(bottom, local_to_global),
                remap_geometry_paths(shape, local_to_global),
                paint,
                remap_geometry_paths(clip, local_to_global),
                transform,
            )
        case SaveLayer(bottom, top, paint):
            return SaveLayer(
                remap_layer_paths(bottom, local_to_global),
                remap_layer_paths(top, local_to_global),
                paint,
            )
        case _:
            return layer


def compile_layer(path: pathlib.Path, global_paths: dict[bytes, int]) -> str:
    with path.open("rb") as f:
        skp = json.load(f)

    layer, path_map = compile_skp_to_lskia(skp["commands"])

    local_to_global: dict[int, int] = {}
    for local_id, skpath in sorted(path_map.items()):
        key = bytes(skpath.serialize())
        if key not in global_paths:
            global_paths[key] = len(global_paths)
        local_to_global[local_id] = global_paths[key]

    layer = remap_layer_paths(layer, local_to_global)
    return layer_to_lean(layer)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("name", help="Layer name, e.g. GitHub__layer_18")
    parser.add_argument("--optj-dir", type=pathlib.Path, default=pathlib.Path("optj"))
    args = parser.parse_args()

    layer_dir = args.optj_dir / args.name
    files = [
        layer_dir / f"{args.name}.json",
        layer_dir / f"{args.name}.01.json",
        layer_dir / f"{args.name}.02.json",
        layer_dir / f"{args.name}.03.json",
        layer_dir / f"{args.name}.04.json",
    ]

    for path in files:
        if not path.exists():
            raise FileNotFoundError(f"Missing input file: {path}")

    global_paths: dict[bytes, int] = {}
    defs = [
        ("src", compile_layer(files[0], global_paths)),
        ("opt1", compile_layer(files[1], global_paths)),
        ("opt2", compile_layer(files[2], global_paths)),
        ("opt3", compile_layer(files[3], global_paths)),
        ("opt4", compile_layer(files[4], global_paths)),
    ]

    prelude = [
        "import MuSkia.LayerTV",
        "",
        f"namespace Generated_{args.name}",
        "",
        "open CoreSk",
        "open Layer",
        "",
        "set_option linter.style.longLine false",
        "set_option linter.style.emptyLine false",
        "",
        "attribute [local irreducible] CoreSk.denote CoreSk.denote_bm CoreSk.denote_filter",
        "attribute [local irreducible] srcover dstin srcin applyAlpha",
        "attribute [local irreducible] Rect RRect Oval ImageRect Path Full TextBlob intersect difference",
    ]

    body = []
    for name, expr in defs:
        body.append(f"def {name} := {expr.replace('Alpha ', 'Pixel.Alpha ')}")

    theorems = [
        "theorem src_eq_opt1 : denote src = denote opt1 := by",
        "  unfold src",
        "  unfold opt1",
        "  grind [GradientMask, GradientMaskRadialTrue, GradientMaskLinearTrue, GradientMaskRadialRRectClip]",
        "",
        "theorem opt1_eq_opt2 : denote opt1 = denote opt2 := by",
        "  unfold opt1",
        "  unfold opt2",
        "  grind (gen := 80) [SubsumeColorFilter_luma_white]",
        "",
        "theorem opt2_eq_opt3 : denote opt2 = denote opt3 := by",
        "  unfold opt2",
        "  unfold opt3",
        "  grind (gen := 80) [clip_mask, is_maskable, MaskIntoDstin]",
        "",
        "theorem opt3_eq_opt4 : denote opt3 = denote opt4 := by",
        "  unfold opt3",
        "  unfold opt4",
        "  grind (gen := 80) [OpaqueSaveLayerRemoveLastDraw, OpaqueSaveLayerEmptyLayer]",
    ]

    sections = [
        "\n".join(prelude),
        "\n\n".join(body),
        "\n".join(theorems),
        f"end Generated_{args.name}",
    ]
    lean_file = "\n\n".join(sections)
    print(lean_file)
