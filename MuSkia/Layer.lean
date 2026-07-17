import MuSkia.Colors

open Pixel

set_option pp.fieldNotation false

namespace CoreSk

/-
Fig 1: Abstract Model
  See lines 13-49.
  Our abstract model also encodes a notion of "Style",
  which describes whether the shape is filled, stroked, or both.
  This extension is discussed in Section 3.4.
-/
def Point : Type := Unit

inductive Image : Type where
  | pixel : Pixel -> Image
  | shader : (Point -> Pixel) -> Image

def getImageFunc (f : Image) : Point -> Pixel :=
match f with
  | Image.pixel px => fun _ => px
  | Image.shader f => f

lemma getImageFunc.pixel (px) (pt) :
  getImageFunc (Image.pixel px) pt = px := rfl

lemma getImageFunc.shader (f) (pt) :
  getImageFunc (Image.shader f) pt = f pt := rfl

def Shape : Type := Point -> Bool

def intersect (g1 g2 : Shape) : Shape := fun pt => g1 pt && g2 pt

def difference (g1 g2 : Shape) : Shape := fun pt => g1 pt && !(g2 pt)

inductive BlendMode : Type where
  | srcover : BlendMode
  | dstin : BlendMode
  | srcin : BlendMode
  | src : BlendMode
  | plus : BlendMode
  | overlay : BlendMode
  | softlight : BlendMode
  | multiply : BlendMode

def Style : Type := Shape -> Shape

inductive Filter : Type where
  | id : Filter
  | custom : (Pixel -> Pixel) -> Filter

/-
Figure 2: Layer Language
  See lines 59-76.
  Paint here differs from the figure,
  because it also includes a Style.
-/
def Paint : Type := Image × BlendMode × Style × Filter

def getAlpha (p : Image) : Real :=
  match p with
  | Image.pixel px => px.1
  | Image.shader _ => 1

lemma getAlpha.pixel (px) :
  getAlpha (Image.pixel px) = px.1 := rfl

lemma getAlpha.shader (f) :
  getAlpha (Image.shader f) = 1 := rfl

inductive Layer : Type where
  | empty : Layer
  | draw  : Layer -> Shape -> Paint -> Shape -> Layer
  | saveLayer  : Layer -> Layer -> Paint -> Layer

open Layer

def countSaveLayers : Layer -> Nat
  | empty => 0
  | draw l_b _ _ _ => countSaveLayers l_b
  | saveLayer l_b l_t _ => countSaveLayers l_b + countSaveLayers l_t + 1

/-
Fig 3: Denotational Semantics
  See lines 90-126.
  denote here differs from the figure,
  because it includes a Style,
  and it also deals with opacity (which is also discussed in Section 3.4).
-/
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
    let drawPx := if (style geo) pt && (clip pt) then ((getImageFunc fill) pt) else Pixel.Transparent
    (denote_bm blend_mode) (l_b pt) (denote_filter filter drawPx)
  | saveLayer l_b l_t paint, pt =>
    let l_b := denote l_b
    let l_t := denote l_t
    let blend_mode : BlendMode := paint.2.1
    let filter     : Filter    := paint.2.2.2
    let alpha      : Real      := getAlpha paint.1
    (denote_bm blend_mode) (l_b pt) (denote_filter filter (applyAlpha alpha (l_t pt)))

notation "⟦" l "⟧" => denote l

/-
Section 4.1: SrcOver SaveLayers
  OpaqueSaveLayerEmptyLayer and OpaqueSaveLayerRemoveLastDraw
  are the two main lemmas that allow us to remove a SaveLayer with an opaque color
  and a SrcOver blend mode. This is the Layer version of this rewrite.
  The muSkia version can be found in SurfaceSk.lean:opaque_saveLayer_denote_eq_save.
-/
@[simp]
theorem OpaqueSaveLayerEmptyLayer l_b :
  denote (saveLayer l_b
                    empty
                    (Image.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
  =
  denote l_b :=
by
  simp only [denote, denote_bm, denote_filter]
  grind [denote_bm, srcover.left_transparent, srcin.on_transparent, applyAlpha]

@[simp]
theorem OpaqueSaveLayerRemoveLastDraw
  (l₁ l₂ : Layer)
  (g clip : Shape)
  (fill : Image)
  (style : Style)
  (filter : Filter) :
  denote
    (saveLayer l₁
      (draw l₂ g (fill, BlendMode.srcover, style, filter) clip)
      (Image.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
  =
  denote
    (draw (saveLayer l₁ l₂ (Image.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
      g (fill, BlendMode.srcover, style, filter) clip) :=
by
  simp only [denote, denote_bm, denote_filter]
  grind [denote, getAlpha.pixel, Alpha.alpha_proj_one, srcover.associative,
    applyAlpha.one]

/-
Section 4.2: Dstin to Clip
  This is the Layer version of the Dstin to Clip rewrite.
  The muSkia version can be found in SurfaceSk.lean:DstinToClip
-/
def is_maskable (l : Layer) : Bool :=
match l with
| .empty => true
| .draw l_b _ (_, BlendMode.srcover, _, Filter.id) _ => is_maskable l_b
| .draw _ _ _ _ => false
| .saveLayer _ _ _ => false

def clip_mask (l : Layer) (m : Shape) : Layer :=
match l with
| .empty => .empty
| .draw l_b g p c => .draw (clip_mask l_b m) g p (intersect c m)
| .saveLayer l1 l2 p => .saveLayer (clip_mask l1 m) (clip_mask l2 m) p

theorem DstinToClip
  (g2 c2 : Shape)
  (color : Pixel)
  (Hopaque : color.a = 1)
  l_b
  (Hmaskable : is_maskable l_b = true) :
  denote
    (Layer.saveLayer l_b
      (Layer.draw Layer.empty g2 (Image.pixel color, BlendMode.srcover, id, Filter.id) c2)
      (Image.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
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
      grind [intersect, getImageFunc.pixel, dstin.right_opaque, srcover.right_transparent,
                       srcover.left_transparent, dstin.right_transparent, Alpha,
                       getAlpha.pixel, applyAlpha.one]
    all_goals simp [is_maskable] at Hmaskable

/-
Section 4.3: Subsume Color Filter
  This is the Layer version of the Subsume Color Filter rewrite.
  The muSkia version can be found in SurfaceSk.lean:SubsumeColorFilter
-/
theorem SubsumeColorFilter
  (g clip : Shape)
  (style : Style)
  (c : Pixel)
  (f : Filter)
  (H : denote_filter f Transparent = Transparent) :
  denote
    (saveLayer empty
      (draw empty g (Image.pixel c, BlendMode.srcover, style, Filter.id) clip)
      (Image.pixel (Alpha 1), BlendMode.srcover, id, f))
  =
  denote
    (draw empty g (Image.pixel (denote_filter f c), BlendMode.srcover, style, Filter.id) clip) :=
by
  simp only [denote, denote_bm, denote_filter.id]
  grind [denote, getImageFunc.pixel, getAlpha.pixel, Alpha.alpha_proj_one, srcover.right_transparent,
    srcin.opaque, applyAlpha.one]

/-
Section 4.4: Gradient Mask
  This is the Layer version of the Gradient Mask rewrite.
  The muSkia version can be found in SurfaceSk.lean:GradientMask
-/
theorem GradientMask
  (shape clip1 clip2 : Shape)
  (style : Style)
  (color : Pixel)
  (gradient : Image)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true)
  (Hopaque : ∀ pt, ((getImageFunc gradient) pt).a = 1) :
  denote
    (saveLayer
      (draw empty shape (Image.pixel color, BlendMode.srcover, style, Filter.id) clip1)
      (draw empty shape (gradient, BlendMode.srcover, style, Filter.id) clip2)
      (Image.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Image.pixel color, BlendMode.srcover, style, Filter.id) clip1) :=
by
  simp only [denote, denote_bm, denote_filter.id]
  grind [denote, getAlpha.pixel, Alpha.alpha_proj_one, srcover.left_transparent,
    srcover.right_opaque, dstin.right_transparent, dstin.right_opaque, applyAlpha.one]

end CoreSk
