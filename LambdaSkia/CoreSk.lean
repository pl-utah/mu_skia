import LambdaSkia.Colors

open Pixel

namespace CoreSk

@[grind, simp]
def Point : Type := Unit

@[grind, simp]
def Geometry : Type := Point -> Bool

@[grind]
inductive Fill : Type where
  | pixel : Pixel -> Fill
  | shader : (Point -> Pixel) -> Fill

@[grind, simp]
def getFillFunc (f : Fill) : Point -> Pixel :=
match f with
  | Fill.pixel px => fun _ => px
  | Fill.shader f => f

@[simp, grind =]
lemma getFillFunc_pixel (px) (pt) :
  getFillFunc (Fill.pixel px) pt = px := rfl

@[simp, grind =]
lemma getFillFunc_shader (f) (pt) :
  getFillFunc (Fill.shader f) pt = f pt := rfl

@[grind, simp]
def BlendMode : Type := Pixel -> Pixel -> Pixel

@[grind, simp]
def Style : Type := Geometry -> Geometry

@[grind, simp]
def Filter : Type := Pixel -> Pixel

@[grind, simp]
def Paint : Type := Fill × BlendMode × Style × Filter

@[grind, simp]
def getAlpha (p : Fill) : Real :=
  match p with
  | Fill.pixel px => px.1
  | Fill.shader _ => 1

@[simp, grind =]
lemma getAlpha_pixel (px) :
  getAlpha (Fill.pixel px) = px.1 := rfl

@[simp, grind =]
lemma getAlpha_shader (f) :
  getAlpha (Fill.shader f) = 1 := rfl

@[grind]
inductive Layer : Type where
  | empty : Layer
  | draw  : Layer -> Geometry -> Paint -> Geometry -> Layer
  | saveLayer  : Layer -> Layer -> Paint -> Layer

open Layer

@[grind, simp]
def denote : Layer -> Point -> Pixel
  | empty, _ => Pixel.Transparent
  | draw l_b geo paint clip, pt =>
    let l_b := denote l_b
    let (fill, blend_mode, style, filter) := paint
    let drawPx := if (style geo) pt && (clip pt) then ((getFillFunc fill) pt) else Pixel.Transparent
    blend_mode (l_b pt) (filter drawPx)
  | saveLayer l_b l_t paint, pt =>
    let l_b := denote l_b
    let l_t := denote l_t
    let blend_mode : BlendMode := paint.2.1
    let filter     : Filter    := paint.2.2.2
    let alpha      : Real      := getAlpha paint.1
    blend_mode (l_b pt) (filter (applyAlpha alpha (l_t pt)))

notation "⟦" l "⟧" => denote l

theorem OpaqueSaveLayerEmptyLayer l_b :
  denote (saveLayer l_b
                    empty
                    (Fill.pixel (Alpha 1), srcover, id, id))
  =
  denote l_b :=
by
  ext pt
  simp

theorem OpaqueSaveLayerRemoveLoneDraw
  (g : Geometry)
  (paint : Paint)
  (clip : Geometry) :
  denote (saveLayer empty
                    (draw empty g paint clip)
                    (Fill.pixel (Alpha 1), srcover, id, id))
  =
  denote (draw empty g paint clip) :=
by
  ext pt
  simp

theorem OpaqueSaveLayerRemoveLastDraw
  (l₁ l₂ : Layer)
  (g clip : Geometry)
  (fill : Fill)
  (style : Style)
  (filter : Filter) :
  denote
    (saveLayer l₁
      (draw l₂ g (fill, srcover, style, filter) clip)
      (Fill.pixel (Alpha 1), srcover, id, id))
  =
  denote
    (draw
      (saveLayer l₁ l₂ (Fill.pixel (Alpha 1), srcover, id, id))
      g (fill, srcover, style, filter) clip) :=
by
  ext pt
  simp
  grind

theorem SubsumeColorFilter
  (g clip : Geometry)
  (style : Style)
  (c : Pixel)
  (f : Filter)
  (H : f Transparent = Transparent) :
  denote
    (saveLayer empty
      (draw empty g (Fill.pixel c, srcover, style, id) clip)
      (Fill.pixel (Alpha 1), srcover, id, f))
  =
  denote
    (draw empty g (Fill.pixel (f c), srcover, style, id) clip) :=
by
  ext pt
  simp
  grind

theorem better_masks
  (shape clip1 clip2 : Geometry)
  (style : Style)
  (color : Pixel)
  (gradient : Fill)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true)
  (Hopaque : ∀ pt, ((getFillFunc gradient) pt).a = 1) :
  denote
    (saveLayer
      (draw empty shape (Fill.pixel color, srcover, style, id) clip1)
      (draw empty shape (gradient, srcover, style, id) clip2)
      (Fill.pixel (Alpha 1), dstin, id, id))
  =
  denote (draw empty shape (Fill.pixel color, srcover, style, id) clip1) :=
by
  ext pt
  simp only [denote]
  grind

end CoreSk
