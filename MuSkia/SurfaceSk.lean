import MuSkia.Layer
import MuSkia.Colors

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

def interp (cmd : Command) (σ : Σ) : Σ :=
  match cmd with
  | skip => σ
  | draw geo paint =>
      match σ.clip_stack, σ.layer_stack with
      | curClip :: _, layer :: layers =>
          { σ with layer_stack := Layer.draw layer geo paint curClip :: layers }
      | _, _ => σ
  | clip geo op =>
      match σ.clip_stack with
      | curClip :: clips =>
          let clip' :=
            match op with
            | ClipOp.int => intersect curClip geo
            | ClipOp.dif => difference curClip geo
          { σ with clip_stack := clip' :: clips }
      | [] => σ
  | save cmd =>
      match σ.clip_stack with
      | curClip :: clips =>
          let σ' := interp cmd { σ with clip_stack := curClip :: curClip :: clips }
          match σ'.clip_stack with
          | _ :: clips' => { σ' with clip_stack := clips' }
          | [] => σ'
      | [] => σ
  | saveLayer paint cmd =>
      match σ.clip_stack, σ.layer_stack with
      | curClip :: clips, layer :: layers =>
          let σ' := interp cmd
            { clip_stack := curClip :: curClip :: clips
            , layer_stack := Layer.empty :: layer :: layers }
          match σ'.clip_stack, σ'.layer_stack with
          | _ :: clips', topLayer :: baseLayer :: layers' =>
              { clip_stack := clips'
              , layer_stack := Layer.saveLayer baseLayer topLayer paint :: layers' }
          | _, _ => σ'
      | _, _ => σ
  | seq cmd₁ cmd₂ => interp cmd₂ (interp cmd₁ σ)

def eval (cmd : Command) : Layer :=
  match (interp cmd { clip_stack := [fun _ => true], layer_stack := [Layer.empty] }).layer_stack with
  | layer :: _ => layer
  | [] => Layer.empty

theorem interp_preserves_stack_lengths (cmd : Command) (σ : Σ) :
  (interp cmd σ).clip_stack.length = σ.clip_stack.length ∧
  (interp cmd σ).layer_stack.length = σ.layer_stack.length := by
  induction cmd generalizing σ with
  | skip =>
      simp [interp]
  | draw _ _ =>
      grind [State, interp]
  | clip _ _ =>
      cases σ with
      | mk clip_stack layer_stack =>
          cases clip_stack <;> simp [interp]
  | save c ih =>
      grind [interp]
  | saveLayer paint c ih =>
      cases σ with
      | mk clip_stack layer_stack =>
          cases clip_stack with
          | nil =>
              simp [interp]
          | cons curClip clips =>
              cases layer_stack with
              | nil =>
                  simp [interp]
              | cons layer layers =>
                  let σ' := interp c
                    { clip_stack := curClip :: curClip :: clips
                    , layer_stack := Layer.empty :: layer :: layers }
                  have hclip : σ'.clip_stack.length = (curClip :: curClip :: clips).length := by
                    simpa [σ'] using (ih
                      { clip_stack := curClip :: curClip :: clips
                      , layer_stack := Layer.empty :: layer :: layers }).1
                  have hlayer : σ'.layer_stack.length = (Layer.empty :: layer :: layers).length := by
                    simpa [σ'] using (ih
                      { clip_stack := curClip :: curClip :: clips
                      , layer_stack := Layer.empty :: layer :: layers }).2
                  cases hstack : σ'.clip_stack with
                  | nil =>
                      simp [σ', hstack] at hclip
                  | cons clip' clips' =>
                      have hcons : (clip' :: clips').length = (curClip :: curClip :: clips).length := by
                        simpa [hstack] using hclip
                      have htail : clips'.length = (curClip :: clips).length := by
                        exact Nat.succ.inj hcons
                      cases hls : σ'.layer_stack <;> grind [interp, Layer, List]
  | seq c₁ c₂ ih₁ ih₂ =>
      constructor
      · exact Eq.trans ((ih₂ (interp c₁ σ)).1) ((ih₁ σ).1)
      · exact Eq.trans ((ih₂ (interp c₁ σ)).2) ((ih₁ σ).2)

theorem interp_preserves_clip_stack_length (cmd : Command) (σ : Σ) :
  (interp cmd σ).clip_stack.length = σ.clip_stack.length := by
  exact (interp_preserves_stack_lengths cmd σ).1

theorem interp_preserves_layer_stack_length (cmd : Command) (σ : Σ) :
  (interp cmd σ).layer_stack.length = σ.layer_stack.length := by
  exact (interp_preserves_stack_lengths cmd σ).2

theorem interp_singleton_clip_stack
  (cmd : Command) (clip : Geometry) (layer : Layer) :
  ∃ clip', (interp cmd ⟨[clip], [layer]⟩).clip_stack = [clip'] := by
  have hlen :
      (interp cmd ⟨[clip], [layer]⟩).clip_stack.length = 1 := by
    simpa using interp_preserves_clip_stack_length cmd ⟨[clip], [layer]⟩
  exact List.length_eq_one_iff.mp hlen

theorem interp_singleton_layer_stack
  (cmd : Command) (clip : Geometry) (layer : Layer) :
  ∃ layer', (interp cmd ⟨[clip], [layer]⟩).layer_stack = [layer'] := by
  have hlen :
      (interp cmd ⟨[clip], [layer]⟩).layer_stack.length = 1 := by
    simpa using interp_preserves_layer_stack_length cmd ⟨[clip], [layer]⟩
  exact List.length_eq_one_iff.mp hlen

theorem interp_singleton_state
  (cmd : Command) (clip : Geometry) (layer : Layer) :
  ∃ clip' layer', interp cmd ⟨[clip], [layer]⟩ = ⟨[clip'], [layer']⟩ := by
  set σ := interp cmd ⟨[clip], [layer]⟩
  rcases interp_singleton_clip_stack cmd clip layer with ⟨clip', hclip⟩
  rcases interp_singleton_layer_stack cmd clip layer with ⟨layer', hlayer⟩
  have hclip' : σ.clip_stack = [clip'] := by
    simpa [σ] using hclip
  have hlayer' : σ.layer_stack = [layer'] := by
    simpa [σ] using hlayer
  cases hσ : σ with
  | mk clip_stack layer_stack =>
      have hclip'' : clip_stack = [clip'] := by
        simpa [hσ] using hclip'
      have hlayer'' : layer_stack = [layer'] := by
        simpa [hσ] using hlayer'
      subst clip_stack
      subst layer_stack
      exact ⟨clip', layer', by simp⟩

theorem eval_never_gets_stuck_strong (cmd : Command) :
  ∃ clip layer,
    interp cmd ⟨[fun _ => true], [Layer.empty]⟩ = ⟨[clip], [layer]⟩ := by
  simpa using interp_singleton_state cmd (fun _ => true) Layer.empty

theorem opaque_saveLayer_skip_denote_eq :
  denote
    (eval
      (saveLayer
        (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)
        skip))
  =
  denote
    (eval skip) := by
  simp [eval, interp, OpaqueSaveLayerEmptyLayer Layer.empty]

set_option pp.fieldNotation false

theorem opaque_saveLayer_draw_denote_eq
  (g : Geometry)
  (fill : Fill)
  (style : Style)
  (filter : Filter) :
  denote
    (eval
      (saveLayer
        (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)
        (draw g (fill, BlendMode.srcover, style, filter))))
  =
  denote
    (eval
      (seq
        (saveLayer
          (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)
          skip)
        (draw g (fill, BlendMode.srcover, style, filter)))) := by
  dsimp [eval, interp]
  exact
    OpaqueSaveLayerRemoveLastDraw
      Layer.empty Layer.empty g (fun _ => true) fill style filter

theorem subsume_colorFilter_draw_denote_eq
  (g : Geometry)
  (c : Pixel)
  (style : Style)
  (f : Filter)
  (H : denote_filter f Pixel.Transparent = Pixel.Transparent) :
  denote
    (eval
      (saveLayer
        (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, f)
        (draw g (Fill.pixel c, BlendMode.srcover, style, Filter.id))))
  =
  denote
    (eval
      (draw g (Fill.pixel (denote_filter f c), BlendMode.srcover, style, Filter.id))) := by
  dsimp [eval, interp]
  simpa using SubsumeColorFilter g (fun _ => true) style c f H

theorem gradientMask_denote_eq
  (shape clip1 clip2 : Geometry)
  (style : Style)
  (color : Pixel)
  (gradient : Fill)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true)
  (Hopaque : ∀ pt, ((getFillFunc gradient) pt).a = 1) :
  denote
    (eval
      (seq
        (save
          (seq
            (clip clip1 ClipOp.int)
            (draw shape (Fill.pixel color, BlendMode.srcover, style, Filter.id))))
        (saveLayer
          (Fill.pixel (Pixel.Alpha 1), BlendMode.dstin, id, Filter.id)
          (seq
            (clip clip2 ClipOp.int)
            (draw shape (gradient, BlendMode.srcover, style, Filter.id)))))) =
  denote
    (eval
      (save
        (seq
          (clip clip1 ClipOp.int)
          (draw shape (Fill.pixel color, BlendMode.srcover, style, Filter.id))))) := by
  dsimp [eval, interp]
  simpa using GradientMask shape clip1 clip2 style color gradient Hsubset Hopaque

inductive PlainDrawList : Command -> Prop where
  | skip :
      PlainDrawList Command.skip
  | seq_draw
      (cmd : Command)
      (hcmd : PlainDrawList cmd)
      (g : Geometry)
      (fill : Fill)
      (style : Style) :
      PlainDrawList
        (Command.seq cmd (Command.draw g (fill, BlendMode.srcover, style, Filter.id)))

theorem plainDrawList_interp_double_empty
  (cmd : Command)
  (hcmd : PlainDrawList cmd) :
  ∃ topLayer,
    interp cmd ⟨[fun _ => true, fun _ => true], [Layer.empty, Layer.empty]⟩
      =
      ⟨[fun _ => true, fun _ => true], [topLayer, Layer.empty]⟩
    ∧
    interp cmd ⟨[fun _ => true, fun _ => true], [Layer.empty]⟩
      =
      ⟨[fun _ => true, fun _ => true], [topLayer]⟩ := by
  induction hcmd with
  | skip =>
      exact ⟨Layer.empty, by simp [interp], by simp [interp]⟩
  | seq_draw cmd hcmd g fill style ih =>
      rcases ih with ⟨topLayer, htwo, hone⟩
      refine ⟨Layer.draw topLayer g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true), ?_, ?_⟩
      · simp [interp, htwo]
      · simp [interp, hone]

theorem plainDrawList_interp_single_empty
  (cmd : Command)
  (hcmd : PlainDrawList cmd) :
  ∃ topLayer,
    interp cmd ⟨[fun _ => true], [Layer.empty]⟩ =
      ⟨[fun _ => true], [topLayer]⟩ := by
  induction hcmd with
  | skip =>
      exact ⟨Layer.empty, by simp [interp]⟩
  | seq_draw cmd hcmd g fill style ih =>
      rcases ih with ⟨topLayer, htop⟩
      refine ⟨Layer.draw topLayer g
          (fill, BlendMode.srcover, style, Filter.id) (fun _ => true), ?_⟩
      simp [interp, htop]

theorem plainDrawList_eval_is_maskable
  (cmd : Command)
  (hcmd : PlainDrawList cmd) :
  is_maskable (eval cmd) = true := by
  induction hcmd with
  | skip =>
      simp [eval, interp, is_maskable]
  | seq_draw cmd hcmd g fill style ih =>
      rcases plainDrawList_interp_single_empty cmd hcmd with ⟨topLayer, hone⟩
      have heval : eval cmd = topLayer := by
        unfold eval
        rw [hone]
      rw [heval] at ih
      simpa [eval, interp, hone, is_maskable] using ih

theorem plainDrawList_interp_clip_mask
  (cmd : Command)
  (hcmd : PlainDrawList cmd)
  (mask : Geometry) :
  ∃ sourceLayer clippedLayer,
    interp cmd ⟨[fun _ => true], [Layer.empty]⟩ =
      ⟨[fun _ => true], [sourceLayer]⟩ ∧
    interp cmd ⟨[mask, fun _ => true], [Layer.empty]⟩ =
      ⟨[mask, fun _ => true], [clippedLayer]⟩ ∧
    denote clippedLayer = denote (clip_mask sourceLayer mask) := by
  induction hcmd with
  | skip =>
      exact ⟨Layer.empty, Layer.empty, by simp [interp], by simp [interp], by simp [clip_mask, denote]⟩
  | seq_draw cmd hcmd g fill style ih =>
      rcases ih with ⟨sourceLayer, clippedLayer, hsource, hclipped, hdenote⟩
      refine
        ⟨Layer.draw sourceLayer g
            (fill, BlendMode.srcover, style, Filter.id) (fun _ => true),
         Layer.draw clippedLayer g
            (fill, BlendMode.srcover, style, Filter.id) mask, ?_, ?_, ?_⟩
      · simp [interp, hsource]
      · simp [interp, hclipped]
      · funext pt
        simp [clip_mask, denote, hdenote, intersect]

theorem maskIntoDstin_denote_eq_clip
  (cmd : Command)
  (hcmd : PlainDrawList cmd)
  (g2 c2 : Geometry)
  (color : Pixel)
  (Hopaque : color.a = 1) :
  denote
    (eval
      (seq cmd
        (saveLayer
          (Fill.pixel (Pixel.Alpha 1), BlendMode.dstin, id, Filter.id)
          (seq
            (clip c2 ClipOp.int)
            (draw g2 (Fill.pixel color, BlendMode.srcover, id, Filter.id))))))
  =
  denote
    (eval
      (save
        (seq
          (clip (intersect g2 c2) ClipOp.int)
          cmd))) := by
  rcases plainDrawList_interp_clip_mask cmd hcmd (intersect g2 c2) with
    ⟨sourceLayer, clippedLayer, hsource, hclipped, hdenote⟩
  have Hmaskable : is_maskable sourceLayer = true := by
    have heval : eval cmd = sourceLayer := by
      unfold eval
      rw [hsource]
    simpa [heval] using plainDrawList_eval_is_maskable cmd hcmd
  have htrue_c2 : intersect (fun _ => true) c2 = c2 := by
    funext pt
    simp [intersect]
  have htrue_mask :
      intersect (fun _ => true) (intersect g2 c2) = intersect g2 c2 := by
    funext pt
    simp [intersect]
  have hfrom :
      denote
        (eval
          (seq cmd
            (saveLayer
              (Fill.pixel (Pixel.Alpha 1), BlendMode.dstin, id, Filter.id)
              (seq
                (clip c2 ClipOp.int)
                (draw g2 (Fill.pixel color, BlendMode.srcover, id, Filter.id))))))
        =
        denote (clip_mask sourceLayer (intersect g2 c2)) := by
    calc
      denote
          (eval
            (seq cmd
              (saveLayer
                (Fill.pixel (Pixel.Alpha 1), BlendMode.dstin, id, Filter.id)
                (seq
                  (clip c2 ClipOp.int)
                  (draw g2 (Fill.pixel color, BlendMode.srcover, id, Filter.id))))))
          =
          denote
            (Layer.saveLayer sourceLayer
              (Layer.draw Layer.empty g2
                (Fill.pixel color, BlendMode.srcover, id, Filter.id) c2)
              (Fill.pixel (Pixel.Alpha 1), BlendMode.dstin, id, Filter.id)) := by
            simp [eval, interp, hsource, htrue_c2]
      _ = denote (clip_mask sourceLayer (intersect g2 c2)) := by
            simpa using
              (MaskIntoDstin g2 c2 color Hopaque sourceLayer Hmaskable)
  calc
    denote
        (eval
          (seq cmd
            (saveLayer
              (Fill.pixel (Pixel.Alpha 1), BlendMode.dstin, id, Filter.id)
              (seq
                (clip c2 ClipOp.int)
                (draw g2 (Fill.pixel color, BlendMode.srcover, id, Filter.id))))))
        = denote (clip_mask sourceLayer (intersect g2 c2)) := hfrom
    _ = denote clippedLayer := hdenote.symm
    _ = denote
        (eval
          (save
            (seq
              (clip (intersect g2 c2) ClipOp.int)
              cmd))) := by
          simp [eval, interp, hclipped, htrue_mask]

theorem opaque_saveLayer_denote_eq_save
  (cmd : Command)
  (hcmd : PlainDrawList cmd) :
  denote
    (eval
      (saveLayer
        (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)
        cmd))
  =
  denote
    (eval
      (save cmd)) := by
  induction hcmd with
  | skip =>
      dsimp [eval, interp]
      simp [OpaqueSaveLayerEmptyLayer Layer.empty]
  | seq_draw cmd hcmd g fill style ih =>
      rcases plainDrawList_interp_double_empty cmd hcmd with ⟨topLayer, htwo, hone⟩
      have hsave :
          denote
            (Layer.saveLayer Layer.empty topLayer
              (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id))
          =
          denote topLayer := by
        simpa [eval, interp, htwo, hone] using ih
      have hdraw :
          denote
            (Layer.draw
              (Layer.saveLayer Layer.empty topLayer
                (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id))
              g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true))
          =
          denote
            (Layer.draw topLayer
              g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true)) := by
        funext pt
        have hsave_pt :
            denote
              (Layer.saveLayer Layer.empty topLayer
                (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)) pt
            =
            denote topLayer pt := by
          exact congrFun hsave pt
        simpa [denote] using
          congrArg
            (fun px =>
              srcover px
                (if style g pt = true then getFillFunc fill pt else Pixel.Transparent))
            hsave_pt
      have hsave_eval :
          eval
            (save
              (seq cmd (draw g (fill, BlendMode.srcover, style, Filter.id))))
          =
          Layer.draw topLayer
            g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true) := by
        simp [eval, interp, hone]
      calc
        denote
          (eval
            (saveLayer
              (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)
              (seq cmd (draw g (fill, BlendMode.srcover, style, Filter.id))))) =
          denote
            (Layer.saveLayer Layer.empty
              (Layer.draw topLayer
                g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true))
              (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id)) := by
            simp [eval, interp, htwo]
        _ =
          denote
            (Layer.draw
              (Layer.saveLayer Layer.empty topLayer
                (Fill.pixel (Pixel.Alpha 1), BlendMode.srcover, id, Filter.id))
              g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true)) := by
            exact
              (OpaqueSaveLayerRemoveLastDraw
                Layer.empty topLayer g (fun _ => true) fill style Filter.id)
        _ =
          denote
            (Layer.draw topLayer
              g (fill, BlendMode.srcover, style, Filter.id) (fun _ => true)) := hdraw
        _ =
          denote
            (eval
              (save
                (seq cmd (draw g (fill, BlendMode.srcover, style, Filter.id))))) := by
            rw [hsave_eval]


end SurfaceSk
