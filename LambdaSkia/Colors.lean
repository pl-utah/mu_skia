import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

@[grind]
structure Pixel where
  a : Real
  r : Real
  g : Real
  b : Real
  valid : 0 <= a /\ a <= 1 /\
          0 <= r /\ r <= a /\
          0 <= g /\ g <= a /\
          0 <= b /\ b <= a

namespace Pixel

@[grind, simp]
def Transparent : Pixel :=
{ a := 0, r := 0, g := 0, b := 0,
  valid := by grind}

@[grind, simp]
def White : Pixel :=
{ a := 1, r := 1, g := 1, b := 1,
  valid := by grind}

@[grind, simp]
def Black : Pixel :=
{ a := 1, r := 0, g := 0, b := 0,
  valid := by grind}

@[grind, simp]
def Alpha (x : Real) : Pixel :=
by
  exact {
    a := min 1 (max 0 x),
    r := 0,
    g := 0,
    b := 0,
    valid := by simp
  }

end Pixel

open Pixel

@[grind, simp]
def srcover (d s : Pixel) : Pixel := {
  a := s.a + d.a * (1 - s.a),
  r := s.r + d.r * (1 - s.a),
  g := s.g + d.g * (1 - s.a),
  b := s.b + d.b * (1 - s.a),
  valid := by
    rcases s.valid with
      ⟨sa0, ⟨sa1, ⟨sr0, ⟨sr1, ⟨sg0, ⟨sg1, ⟨sb0, sb1⟩⟩⟩⟩⟩⟩⟩
    rcases d.valid with
      ⟨da0, ⟨da1, ⟨dr0, ⟨dr1, ⟨dg0, ⟨dg1, ⟨db0, db1⟩⟩⟩⟩⟩⟩⟩
    repeat' constructor
    all_goals nlinarith
}

@[grind =, simp]
theorem srcover.left_transparent (d : Pixel) :
  srcover d Transparent = d :=
by
  grind

@[grind =, simp]
theorem srcover.right_transparent (s : Pixel) :
  srcover Transparent s = s :=
by
  grind

@[grind =, simp]
theorem srcover.right_opaque (d s : Pixel) (h : s.a = 1) :
  srcover d s = s :=
by
  grind

@[grind =, simp]
theorem srcover.associative (d₁ d₂ s : Pixel) :
  srcover (srcover d₁ d₂) s = srcover d₁ (srcover d₂ s) :=
by
  grind

@[simp]
theorem srcover.luminance_white (d : Pixel) (f : Pixel -> Pixel) (h : f White = Black) :
  f (srcover d White) = srcover (f d) Black :=
by
  grind

-- r = d * sa
@[grind, simp]
def dstin (d s : Pixel) : Pixel := {
  a := d.a * s.a,
  r := d.r * s.a,
  g := d.g * s.a,
  b := d.b * s.a,
  valid := by
    rcases s.valid with
      ⟨sa0, ⟨sa1, ⟨sr0, ⟨sr1, ⟨sg0, ⟨sg1, ⟨sb0, sb1⟩⟩⟩⟩⟩⟩⟩
    rcases d.valid with
      ⟨da0, ⟨da1, ⟨dr0, ⟨dr1, ⟨dg0, ⟨dg1, ⟨db0, db1⟩⟩⟩⟩⟩⟩⟩
    repeat' constructor
    all_goals nlinarith
}

@[grind =, simp]
theorem dstin.left_transparent (s : Pixel) :
  dstin Transparent s = Transparent :=
by
  grind

@[grind =, simp]
theorem dstin.right_transparent (d : Pixel) :
  dstin d Transparent = Transparent :=
by
  grind

@[grind =, simp]
theorem dstin.right_opaque (d s : Pixel) (h : s.a = 1) :
  dstin d s = d :=
by
  grind

@[simp]
theorem dstin.right_opaque_general (T : Type) (d : Pixel) (pt : T) (f : T -> Pixel)
  (h : (f pt).a = 1) :
  dstin d (f pt) = d :=
by
  grind

@[grind, simp]
def src (_ s : Pixel) : Pixel := {
  a := s.a,
  r := s.r,
  g := s.g,
  b := s.b,
  valid := by
    rcases s.valid with
      ⟨sa0, ⟨sa1, ⟨sr0, ⟨sr1, ⟨sg0, ⟨sg1, ⟨sb0, sb1⟩⟩⟩⟩⟩⟩⟩
    repeat' constructor
    all_goals nlinarith
}

theorem src.def (d s : Pixel) :
  src d s = s :=
by
  grind

@[grind, simp]
def srcin (d s : Pixel) : Pixel := {
  a := d.a * s.a,
  r := d.r * s.a,
  g := d.g * s.a,
  b := d.b * s.a,
  valid := by
    rcases s.valid with
      ⟨sa0, ⟨sa1, ⟨sr0, ⟨sr1, ⟨sg0, ⟨sg1, ⟨sb0, sb1⟩⟩⟩⟩⟩⟩⟩
    rcases d.valid with
      ⟨da0, ⟨da1, ⟨dr0, ⟨dr1, ⟨dg0, ⟨dg1, ⟨db0, db1⟩⟩⟩⟩⟩⟩⟩
    repeat' constructor
    all_goals nlinarith
}

@[grind =, simp]
theorem srcin.opaque (d s : Pixel) (h : s.a = 1) :
  srcin d s = d :=
by
  grind

@[grind =, simp]
theorem srcin.transparent (d : Pixel) :
  srcin d Transparent = Transparent :=
by
  grind

@[simp]
theorem srcin.on_transparent (s : Pixel) :
  srcin Transparent s = Transparent :=
by
  grind

@[grind, simp]
def applyAlpha (alpha : Real) (c : Pixel) : Pixel :=
  srcin c (Alpha alpha)
