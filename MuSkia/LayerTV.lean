import MuSkia.Layer
import MuSkia.Colors

/-
This is a helper file for Translation Validation.
This containes a few definitions of various
concrete objects and properties of the various types in the abstract model.
As we only need to reason about their existence and their type,
their definitions are not important, and are therefore left as `sorry` or axiomatized.
They are not part of the main formalization, and only used for translation validation.
-/

open CoreSk
open Layer
open Pixel

def Rect (x y w h : Float) : Shape := sorry
def RRect (x y w h a b c d : Float) : Shape := sorry
def Oval (l t r b : Float) : Shape := sorry
def TextBlob (x y w h a b : Float) : Shape := sorry
def ImageRect (l t r b : Float) : Shape := sorry
def Path (b : Float) : Shape := sorry
def Full : Shape := sorry

def stroke : Style := sorry

def LinearGradient (isOpaque : Bool) : Point -> Pixel := sorry

def RadialGradient (isOpaque : Bool) : Point -> Pixel := sorry

@[grind, simp]
axiom LinearGradient.opaque (pt : Point) :
  (LinearGradient true pt).a = 1

@[grind, simp]
axiom RadialGradient.opaque (pt : Point) :
  (RadialGradient true pt).a = 1

@[grind, simp]
theorem LinearGradientFill.opaque (pt : Point) :
  ((getImageFunc (Image.shader (LinearGradient true))) pt).a = 1 := by
  simp [CoreSk.getImageFunc, LinearGradient.opaque]

@[grind, simp]
theorem RadialGradientFill.opaque (pt : Point) :
  ((getImageFunc (Image.shader (RadialGradient true))) pt).a = 1 := by
  simp [CoreSk.getImageFunc, RadialGradient.opaque]

@[grind, simp]
theorem GradientMaskRadialTrue
  (shape clip1 clip2 : Shape)
  (style : Style)
  (color : Pixel)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true) :
  denote
    (saveLayer
      (draw empty shape (Image.pixel color, BlendMode.srcover, style, Filter.id) clip1)
      (draw empty shape
                  (Image.shader (RadialGradient true), BlendMode.srcover, style, Filter.id) clip2)
      (Image.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Image.pixel color, BlendMode.srcover, style, Filter.id) clip1) := by
  apply GradientMask shape clip1 clip2 style color (Image.shader (RadialGradient true)) Hsubset
  intro pt
  simp [RadialGradientFill.opaque pt]

@[grind, simp]
theorem GradientMaskLinearTrue
  (shape clip1 clip2 : Shape)
  (style : Style)
  (color : Pixel)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true) :
  denote
    (saveLayer
      (draw empty shape (Image.pixel color, BlendMode.srcover, style, Filter.id) clip1)
      (draw empty shape (Image.shader (LinearGradient true), BlendMode.srcover, style, Filter.id) clip2)
      (Image.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Image.pixel color, BlendMode.srcover, style, Filter.id) clip1) := by
  apply GradientMask shape clip1 clip2 style color (Image.shader (LinearGradient true)) Hsubset
  intro pt
  simpa using LinearGradientFill.opaque pt

@[grind, simp]
theorem GradientMaskRadialRRectClip
  (shape mask : Shape)
  (color : Pixel) :
  denote
    (saveLayer
      (draw empty shape (Image.pixel color, BlendMode.srcover, id, Filter.id) (intersect Full mask))
      (draw empty mask (Image.shader (RadialGradient true), BlendMode.srcover, id, Filter.id) Full)
      (Image.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Image.pixel color, BlendMode.srcover, id, Filter.id) (intersect Full mask)) := by
  funext pt
  by_cases hdraw : shape pt = true ∧ intersect Full mask pt = true
  · have hmaskfull : mask pt = true ∧ Full pt = true := by
      have hfullmask : Full pt = true ∧ mask pt = true := by
        simpa [CoreSk.intersect] using hdraw.2
      exact ⟨hfullmask.2, hfullmask.1⟩
    have hα :
        (applyAlpha (getAlpha (Image.pixel (Alpha 1)))
          (getImageFunc (Image.shader (RadialGradient true)) pt)).a = 1 := by
      simp [getAlpha.pixel, Alpha.alpha_proj_one, applyAlpha.one, RadialGradientFill.opaque]
    have hdst :
        dstin (getImageFunc (Image.pixel color) pt)
          (applyAlpha (getAlpha (Image.pixel (Alpha 1)))
            (getImageFunc (Image.shader (RadialGradient true)) pt))
        = getImageFunc (Image.pixel color) pt :=
      dstin.right_opaque _ _ hα
    simp [denote, denote_bm, denote_filter, hdraw, hmaskfull, hdst, srcover.right_transparent]
  · simp [denote, denote_bm, denote_filter, hdraw, applyAlpha.one, srcover.right_transparent,
      dstin.left_transparent]

def LumaFilter : Pixel -> Pixel := sorry

@[grind, simp]
axiom LumaFilter.transparent :
  LumaFilter Transparent = Transparent

@[grind, simp]
axiom LumaFilter.white_black :
  LumaFilter White = Black

@[grind, simp]
axiom LumaFilter.white_literal :
  LumaFilter ⟨1, 1.0, 1.0, 1.0, by norm_num⟩ = ⟨1, 0.0, 0.0, 0.0, by norm_num⟩

@[grind, simp]
theorem SubsumeColorFilter_luma_white (g clip : Shape) :
  denote
    (saveLayer empty
      (draw empty g
        (Image.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id)
        clip)
      (Image.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.custom LumaFilter))
  =
  denote
    (draw empty g
      (Image.pixel ⟨1, 0.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id)
      clip) :=
by
  have Ht : denote_filter (Filter.custom LumaFilter) Transparent = Transparent := by
    simpa [denote_filter] using LumaFilter.transparent
  simpa [denote_filter, LumaFilter.white_literal] using
    (SubsumeColorFilter g clip id ⟨1, 1.0, 1.0, 1.0, by norm_num⟩ (Filter.custom LumaFilter) Ht)

@[grind, simp]
axiom intersect.Full_right (g : Shape) :
  intersect g Full = g

@[grind, simp]
theorem intersect.assoc (a b c : Shape) :
  intersect (intersect a b) c = intersect a (intersect b c) :=
by
  funext pt
  simp [CoreSk.intersect, Bool.and_assoc]

@[grind, simp]
theorem intersect.comm (a b : Shape) :
  intersect a b = intersect b a :=
by
  funext pt
  simp [CoreSk.intersect, Bool.and_comm]

@[grind, simp]
theorem intersect.idem (a : Shape) :
  intersect a a = a :=
by
  funext pt
  simp [CoreSk.intersect]

@[grind ., simp]
theorem denote_in_draw l l' g p c :
  denote l = denote l' ->
  denote (draw l g p c) = denote (draw l' g p c) :=
by
  intro H
  simp [denote, H]

@[grind ., simp]
theorem denote_in_saveLayer l1 l1' l2 l2' p :
  denote l1 = denote l1' ->
  denote l2 = denote l2' ->
  denote (saveLayer l1 l2 p) = denote (saveLayer l1' l2' p) :=
by
  intros H1 H2
  simp [denote, H1, H2]
