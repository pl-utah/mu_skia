import LambdaSkia.Layer
import LambdaSkia.Colors

open CoreSk
open Layer
open Pixel

def Rect (x y w h : Float) : Geometry := sorry
def RRect (x y w h a b c d : Float) : Geometry := sorry
def TextBlob (x y w h a b : Float) : Geometry := sorry
def ImageRect (l t r b : Float) : Geometry := sorry
def Path (b : Float) : Geometry := sorry
def Full : Geometry := sorry

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
  ((getFillFunc (Fill.shader (LinearGradient true))) pt).a = 1 := by
  simp [CoreSk.getFillFunc, LinearGradient.opaque]

@[grind, simp]
theorem RadialGradientFill.opaque (pt : Point) :
  ((getFillFunc (Fill.shader (RadialGradient true))) pt).a = 1 := by
  simp [CoreSk.getFillFunc, RadialGradient.opaque]

@[grind, simp]
theorem GradientMaskRadialTrue
  (shape clip1 clip2 : Geometry)
  (style : Style)
  (color : Pixel)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true) :
  denote
    (saveLayer
      (draw empty shape (Fill.pixel color, BlendMode.srcover, style, Filter.id) clip1)
      (draw empty shape (Fill.shader (RadialGradient true), BlendMode.srcover, style, Filter.id) clip2)
      (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Fill.pixel color, BlendMode.srcover, style, Filter.id) clip1) := by
  apply GradientMask shape clip1 clip2 style color (Fill.shader (RadialGradient true)) Hsubset
  intro pt
  simpa using RadialGradientFill.opaque pt

@[grind, simp]
theorem GradientMaskLinearTrue
  (shape clip1 clip2 : Geometry)
  (style : Style)
  (color : Pixel)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true) :
  denote
    (saveLayer
      (draw empty shape (Fill.pixel color, BlendMode.srcover, style, Filter.id) clip1)
      (draw empty shape (Fill.shader (LinearGradient true), BlendMode.srcover, style, Filter.id) clip2)
      (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  =
  denote (draw empty shape (Fill.pixel color, BlendMode.srcover, style, Filter.id) clip1) := by
  apply GradientMask shape clip1 clip2 style color (Fill.shader (LinearGradient true)) Hsubset
  intro pt
  simpa using LinearGradientFill.opaque pt

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
theorem SubsumeColorFilter_luma_white (g clip : Geometry) :
  denote
    (saveLayer empty
      (draw empty g
        (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id)
        clip)
      (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.custom LumaFilter))
  =
  denote
    (draw empty g
      (Fill.pixel ⟨1, 0.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id)
      clip) :=
by
  have Ht : denote_filter (Filter.custom LumaFilter) Transparent = Transparent := by
    simpa [denote_filter] using LumaFilter.transparent
  simpa [denote_filter, LumaFilter.white_literal] using
    (SubsumeColorFilter g clip id ⟨1, 1.0, 1.0, 1.0, by norm_num⟩ (Filter.custom LumaFilter) Ht)

@[grind, simp]
axiom intersect.Full_right (g : Geometry) :
  intersect g Full = g

@[grind, simp]
theorem intersect.assoc (a b c : Geometry) :
  intersect (intersect a b) c = intersect a (intersect b c) :=
by
  funext pt
  simp [CoreSk.intersect, Bool.and_assoc]

@[grind, simp]
theorem intersect.comm (a b : Geometry) :
  intersect a b = intersect b a :=
by
  funext pt
  simp [CoreSk.intersect, Bool.and_comm]

@[grind, simp]
theorem intersect.idem (a : Geometry) :
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
