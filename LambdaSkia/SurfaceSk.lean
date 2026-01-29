import LambdaSkia.CoreSk
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
  | saveLayer : SavePaint -> Command -> Command

open Command

structure CanvasState where
  clip : Geometry
  prevState : CanvasState
  surface : Layer

def interp (state : CanvasState) (cmd : Command) : CanvasState :=
  match cmd with
  | skip => state
  | draw geo paint => {
      clip := state.clip,
      prevState := state.prevState,
      surface := Layer.draw state.surface geo paint state.clip
    }
  | clip geo ClipOp.int => {
      clip := fun pt => geo pt && state.clip pt,
      prevState := state.prevState,
      surface := state.surface
    }
  | clip geo ClipOp.dif => {
      clip := fun pt => geo pt && !(state.clip pt),
      prevState := state.prevState,
      surface := state.surface
    }
  | save _ =>
    let inner_state := interp {

    }
  | saveLayer paint inner_cmd =>
    let inner_state := interp {
      clip := state.clip,
      surface := Layer.empty,
      prevState := state,
    } inner_cmd
    {
      clip := state.clip,
      surface := Layer.saveLayer state.surface inner_state.surface paint,
      prevState := state.prevState,
    }

end SurfaceSk
