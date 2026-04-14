import LambdaSkia.Colors

open Pixel

set_option pp.fieldNotation false

namespace CoreSk

def Point : Type := Unit

def Geometry : Type := Point -> Bool

def intersect (g1 g2 : Geometry) : Geometry := fun pt => g1 pt && g2 pt

def difference (g1 g2 : Geometry) : Geometry := fun pt => g1 pt && !(g2 pt)

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
  | plus : BlendMode
  | overlay : BlendMode
  | softlight : BlendMode
  | multiply : BlendMode

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
noncomputable def denote_bm (bm : BlendMode) : Pixel -> Pixel -> Pixel :=
  match bm with
  | BlendMode.srcover => srcover
  | BlendMode.dstin => dstin
  | BlendMode.srcin => srcin
  | BlendMode.src => src
  | BlendMode.plus => plus
  | BlendMode.overlay => overlay
  | BlendMode.softlight => softlight
  | BlendMode.multiply => multiply

@[simp]
def denote_filter (f : Filter) : Pixel -> Pixel :=
  match f with
  | Filter.id => id
  | Filter.custom f => f

def denote_filter.id (px : Pixel) :
  denote_filter Filter.id px = px := rfl

noncomputable def denote : Layer -> Point -> Pixel
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
  (l₁ l₂ : Layer)
  (g clip : Geometry)
  (fill : Fill)
  (style : Style)
  (filter : Filter) :
  denote
    (saveLayer l₁
      (draw l₂ g (fill, BlendMode.srcover, style, filter) clip)
      (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
  =
  denote
    (draw (saveLayer l₁ l₂ (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
      g (fill, BlendMode.srcover, style, filter) clip) :=
by
  simp only [denote, denote_bm, denote_filter]
  grind [denote, getAlpha.pixel, Alpha.alpha_proj_one, srcover.associative,
    applyAlpha.one]

#print OpaqueSaveLayerRemoveLastDraw._proof_1_6

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

theorem GradientMask
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

def is_maskable (l : Layer) : Bool :=
match l with
| .empty => true
| .draw l_b _ (_, BlendMode.srcover, _, Filter.id) _ => is_maskable l_b
| .draw _ _ _ _ => false
| .saveLayer _ _ _ => false

def clip_mask (l : Layer) (m : Geometry) : Layer :=
match l with
| .empty => .empty
| .draw l_b g p c => .draw (clip_mask l_b m) g p (intersect c m)
| .saveLayer l1 l2 p => .saveLayer (clip_mask l1 m) (clip_mask l2 m) p

theorem MaskIntoDstin
  (g2 c2 : Geometry)
  (color : Pixel)
  (Hopaque : color.a = 1)
  l_b
  (Hmaskable : is_maskable l_b = true) :
  denote
    (Layer.saveLayer l_b
      (Layer.draw Layer.empty g2 (Fill.pixel color, BlendMode.srcover, id, Filter.id) c2)
      (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  = denote (clip_mask l_b (intersect g2 c2)) :=
by
  -- induction on structure of Hmaskable
  induction l_b with
  | saveLayer l1 l2 p IH =>
    simp [is_maskable] at Hmaskable
  | empty =>
    simp [clip_mask, denote]
    grind [dstin.left_transparent]
  | draw l g p c IH =>
    rcases p with ⟨fill, bm, s, filter⟩
    cases bm <;> cases filter
    · simp only [is_maskable] at Hmaskable
      have IH' := IH Hmaskable
      simp only [clip_mask]
      simp only [denote] at *
      simp only [denote_bm, denote_filter, Alpha, zero_le_one, sup_of_le_right, min_self,
                 getAlpha.pixel, id_eq, Bool.and_eq_true, applyAlpha.one] at *
      grind [intersect, getFillFunc.pixel, dstin.right_opaque, srcover.right_transparent,
                       srcover.left_transparent, dstin.right_transparent, Alpha,
                       getAlpha.pixel, applyAlpha.one]
    all_goals simp [is_maskable] at Hmaskable

end CoreSk
