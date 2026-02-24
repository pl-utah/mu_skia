import LambdaSkia.Layer
import LambdaSkia.Colors

namespace SurfaceSk

open CoreSk

inductive ClipOp : Type where
  | int : ClipOp
  | dif : ClipOp

inductive Command : Type where
  | skip : Command
  | draw : Geometry -> Paint -> Command
  | clip : Geometry -> ClipOp -> Command
  | save : Command -> Command
  | saveLayer : Paint -> Command -> Command
  | seq : Command -> Command -> Command

open Command

structure State where
  clip_stack : List Geometry
  layer_stack : List Layer

notation "Σ" => State

-- function or inductive predicate?

/-
theorem:
∃ L, C such that
⟨cmd, ⟨[Empty], [Full]⟩⟩ -> ⟨[L], [C]⟩

this means that -> never gets stuck, and we get a single layer back.

OR

theorem:
∃ L, C such that
interp(cmd, ⟨[Empty], [Full]⟩) = ⟨[L], [C]⟩
-/

end SurfaceSk
