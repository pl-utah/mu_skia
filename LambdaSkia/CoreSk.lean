import LambdaSkia.Colors

open Pixel

set_option pp.fieldNotation false

namespace CoreSk

def Point : Type := Unit

def Geometry : Type := Point -> Bool

def intersect (g1 g2 : Geometry) : Geometry := fun pt => g1 pt && g2 pt

inductive Fill : Type where
  | pixel : Pixel -> Fill
  | shader : (Point -> Pixel) -> Fill

def getFillFunc (f : Fill) : Point -> Pixel :=
match f with
  | Fill.pixel px => fun _ => px
  | Fill.shader f => f

lemma getFillFunc.pixel (px) (pt) :
  getFillFunc (Fill.pixel px) pt = px := rfl

lemma getFillFunc.shader (f) (pt) :
  getFillFunc (Fill.shader f) pt = f pt := rfl

-- def BlendMode : Type := Pixel -> Pixel -> Pixel
inductive BlendMode : Type where
  | srcover : BlendMode
  | dstin : BlendMode
  | srcin : BlendMode
  | src : BlendMode

def Style : Type := Geometry -> Geometry

-- def Filter : Type := Pixel -> Pixel
inductive Filter : Type where
  | id : Filter
  | custom : (Pixel -> Pixel) -> Filter

def Paint : Type := Fill × BlendMode × Style × Filter

def getAlpha (p : Fill) : Real :=
  match p with
  | Fill.pixel px => px.1
  | Fill.shader _ => 1

lemma getAlpha.pixel (px) :
  getAlpha (Fill.pixel px) = px.1 := rfl

lemma getAlpha.shader (f) :
  getAlpha (Fill.shader f) = 1 := rfl

inductive Layer : Type where
  | empty : Layer
  | draw  : Layer -> Geometry -> Paint -> Geometry -> Layer
  | saveLayer  : Layer -> Layer -> Paint -> Layer

open Layer

def countSaveLayers : Layer -> Nat
  | empty => 0
  | draw l_b _ _ _ => countSaveLayers l_b
  | saveLayer l_b l_t _ => countSaveLayers l_b + countSaveLayers l_t + 1

@[simp]
def denote_bm (bm : BlendMode) : Pixel -> Pixel -> Pixel :=
  match bm with
  | BlendMode.srcover => srcover
  | BlendMode.dstin => dstin
  | BlendMode.srcin => srcin
  | BlendMode.src => src

@[simp]
def denote_filter (f : Filter) : Pixel -> Pixel :=
  match f with
  | Filter.id => id
  | Filter.custom f => f

def denote_filter.id (px : Pixel) :
  denote_filter Filter.id px = px := rfl

def denote : Layer -> Point -> Pixel
  | empty, _ => Pixel.Transparent
  | draw l_b geo paint clip, pt =>
    let l_b := denote l_b
    let (fill, blend_mode, style, filter) := paint
    let drawPx := if (style geo) pt && (clip pt) then ((getFillFunc fill) pt) else Pixel.Transparent
    (denote_bm blend_mode) (l_b pt) (denote_filter filter drawPx)
  | saveLayer l_b l_t paint, pt =>
    let l_b := denote l_b
    let l_t := denote l_t
    let blend_mode : BlendMode := paint.2.1
    let filter     : Filter    := paint.2.2.2
    let alpha      : Real      := getAlpha paint.1
    (denote_bm blend_mode) (l_b pt) (denote_filter filter (applyAlpha alpha (l_t pt)))

notation "⟦" l "⟧" => denote l

@[simp]
theorem OpaqueSaveLayerEmptyLayer l_b :
  denote (saveLayer l_b
                    empty
                    (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
  =
  denote l_b :=
by
  simp only [denote, denote_bm, denote_filter]
  grind [denote_bm, srcover.left_transparent, srcin.on_transparent, applyAlpha]

@[simp]
theorem OpaqueSaveLayerRemoveLastDraw
  (l₁ l₂ lp: Layer)
  (g clip : Geometry)
  (fill : Fill)
  (style : Style)
  (filter : Filter)
  (Hp : denote lp = denote (saveLayer l₁ l₂ (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
) :
  denote
    (saveLayer l₁
      (draw l₂ g (fill, BlendMode.srcover, style, filter) clip)
      (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
  =
  denote
    (draw lp
      g (fill, BlendMode.srcover, style, filter) clip) :=
by
  simp only [Hp, denote, denote_bm, denote_filter]
  grind [denote, getAlpha.pixel, Alpha.alpha_proj_one, srcover.associative,
    applyAlpha.one]

theorem SubsumeColorFilter
  (g clip : Geometry)
  (style : Style)
  (c : Pixel)
  (f : Filter)
  (H : denote_filter f Transparent = Transparent) :
  denote
    (saveLayer empty
      (draw empty g (Fill.pixel c, BlendMode.srcover, style, Filter.id) clip)
      (Fill.pixel (Alpha 1), BlendMode.srcover, id, f))
  =
  denote
    (draw empty g (Fill.pixel (denote_filter f c), BlendMode.srcover, style, Filter.id) clip) :=
by
  simp only [denote, denote_bm, denote_filter.id]
  grind [denote, getFillFunc.pixel, getAlpha.pixel, Alpha.alpha_proj_one, srcover.right_transparent,
    srcin.opaque, applyAlpha.one]

theorem better_masks
  (shape clip1 clip2 : Geometry)
  (style : Style)
  (color : Pixel)
  (gradient : Fill)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true)
  (Hopaque : ∀ pt, ((getFillFunc gradient) pt).a = 1) :
  denote
    (saveLayer
      (draw empty shape (Fill.pixel color, BlendMode.srcover, style, Filter.id) clip1)
      (draw empty shape (gradient, BlendMode.srcover, style, Filter.id) clip2)
      (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Fill.pixel color, BlendMode.srcover, style, Filter.id) clip1) :=
by
  simp only [denote, denote_bm, denote_filter.id]
  grind [denote, getAlpha.pixel, Alpha.alpha_proj_one, srcover.left_transparent,
    srcover.right_opaque, dstin.right_transparent, dstin.right_opaque, applyAlpha.one]

end CoreSk
