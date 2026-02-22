import LambdaSkia.CoreSk
import LambdaSkia.Colors

set_option linter.style.setOption false
set_option pp.fieldNotation false

open CoreSk
open Layer
open Pixel

def Rect (x y w h : Float) : Geometry := sorry
def RRect (x y w h a b c d : Float) : Geometry := sorry
def TextBlob (x y w h a b : Float) : Geometry := sorry
def Path (b : Float) : Geometry := sorry
def Full : Geometry := sorry

def LumaFilter : Pixel -> Pixel := sorry

@[grind, simp]
axiom intersect.Full_right (g : Geometry) :
  intersect g Full = g

@[grind]
inductive Clips (mask : Geometry) : Layer -> Layer -> Prop where
| empty : Clips mask Layer.empty Layer.empty
| draw  :
    ∀ l1 l2 g fill style clip,
      Clips mask l1 l2 ->
      Clips mask
        (Layer.draw l1 g (fill, BlendMode.srcover, style, Filter.id) clip)
        (Layer.draw l2 g (fill, BlendMode.srcover, style, Filter.id) (intersect clip mask))

theorem MaskIntoDstin
  (g2 c2 : Geometry)
  (color : Pixel)
  (Hopaque : color.a = 1)
  (bottom1 bottom2 : Layer)
  (Hclip : Clips (intersect g2 c2) bottom1 bottom2) :
  denote
    (Layer.saveLayer bottom1
      (Layer.draw Layer.empty g2 (Fill.pixel color, BlendMode.srcover, id, Filter.id) c2)
      (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id))
  = denote bottom2 := by
  induction Hclip <;>
  simp [denote, denote_bm] at * <;>
  grind [intersect, Alpha, getAlpha.pixel, applyAlpha.one, getFillFunc.pixel,
         dstin.right_opaque, srcover.right_transparent,
         srcover.left_transparent, dstin.right_transparent,
         dstin.left_transparent]

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

theorem testing :
  denote (saveLayer (draw empty (Rect 150 70 200 120)
              (Fill.pixel ⟨1, 1, 0, 0, by norm_num⟩,
               BlendMode.srcover,
               id,
               Filter.id)
               Full)
            (draw empty (Rect 170 70 220 120)
              (Fill.pixel ⟨0.30196078431372547, 0, 0, 0.30196078431372547,
                                           by norm_num⟩,
               BlendMode.srcover,
               id,
               Filter.id)
               Full)
            (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id))
=
  denote (draw (draw empty (Rect 150 70 200 120)
              (Fill.pixel ⟨1, 1, 0, 0, by norm_num⟩,
               BlendMode.srcover,
               id,
               Filter.id)
               Full)
   (Rect 170 70 220 120)
              (Fill.pixel ⟨0.30196078431372547, 0, 0, 0.30196078431372547,
                                           by norm_num⟩,
               BlendMode.srcover,
               id,
               Filter.id)
               Full) :=
by
  grind [OpaqueSaveLayerRemoveLastDraw, OpaqueSaveLayerEmptyLayer]

theorem testing_2 :
  denote (saveLayer (draw (draw empty (Rect 10.0 70.0 60.0 120.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Rect 150.0 70.0 200.0 120.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (draw (draw empty (Rect 30.0 70.0 80.0 120.0) (Fill.pixel ⟨1.0, 0.0, 0.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Rect 170.0 70.0 220.0 120.0) (Fill.pixel ⟨0.30196078431372547, 0.0, 0.0, 0.30196078431372547, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id) )
  =
  denote (draw (draw (draw (draw empty (Rect 10.0 70.0 60.0 120.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Rect 150.0 70.0 200.0 120.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Rect 30.0 70.0 80.0 120.0) (Fill.pixel ⟨1.0, 0.0, 0.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Rect 170.0 70.0 220.0 120.0) (Fill.pixel ⟨0.30196078431372547, 0.0, 0.0, 0.30196078431372547, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) :=
by
  grind [OpaqueSaveLayerRemoveLastDraw, OpaqueSaveLayerEmptyLayer]

#print testing_2._proof_1_4

theorem testing_3 :
  denote (saveLayer (draw empty (Rect 0.0 0.0 192.0 192.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (draw empty (Rect 64.0 64.0 128.0 128.0) (Fill.pixel ⟨1, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id) )
  =
  denote (draw empty (Rect 0.0 0.0 192.0 192.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 64.0 64.0 128.0 128.0)))
  :=
by
  grind [MaskIntoDstin]

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

set_option pp.fieldNotation false

theorem MaskIntoDstin2
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

theorem testing_4 :
  denote (saveLayer (draw empty (Rect 0.0 0.0 192.0 192.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (draw empty (Rect 64.0 64.0 128.0 128.0) (Fill.pixel ⟨1, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id) )
  =
  denote (draw empty (Rect 0.0 0.0 192.0 192.0) (Fill.pixel ⟨1.0, 1.0, 0.0, 0.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 64.0 64.0 128.0 128.0)))
  :=
by
  grind [clip_mask, is_maskable, MaskIntoDstin2]

theorem github_18 :
  denote (draw (saveLayer (draw empty Full (Fill.pixel ⟨0.0, 0.0, 0.0, 0.0, by norm_num⟩, BlendMode.src, id, Filter.id) Full ) (draw (draw empty (Rect 1220.0 0.0 1256.0 36.0) (Fill.pixel ⟨0.7490196078431373, 0.03818531334102268, 0.049934640522875814, 0.06755863129565552, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (RRect 1221.0 1.0 1255.0 35.0 17.0 17.0 17.0 17.0)) ) (Path 0) (Fill.pixel ⟨0.14901960784313725, 0.14901960784313725, 0.14901960784313725, 0.14901960784313725, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (RRect 1220.0 0.0 1256.0 36.0 18.0 18.0 18.0 18.0)) ) (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id) ) (Path 1) (Fill.pixel ⟨0.6, 0.6, 0.6, 0.6, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full )
  =
  denote (draw (draw (draw (draw empty Full (Fill.pixel ⟨0.0, 0.0, 0.0, 0.0, by norm_num⟩, BlendMode.src, id, Filter.id) Full ) (Rect 1220.0 0.0 1256.0 36.0) (Fill.pixel ⟨0.7490196078431373, 0.03818531334102268, 0.049934640522875814, 0.06755863129565552, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (RRect 1221.0 1.0 1255.0 35.0 17.0 17.0 17.0 17.0)) ) (Path 0) (Fill.pixel ⟨0.14901960784313725, 0.14901960784313725, 0.14901960784313725, 0.14901960784313725, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (RRect 1220.0 0.0 1256.0 36.0 18.0 18.0 18.0 18.0)) ) (Path 1) (Fill.pixel ⟨0.6, 0.6, 0.6, 0.6, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full )
  :=
by
  grind [OpaqueSaveLayerRemoveLastDraw,OpaqueSaveLayerEmptyLayer]

theorem pinterest_108 :
  denote (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (saveLayer (draw (draw (draw (draw empty Full (Fill.pixel ⟨0.0, 0.0, 0.0, 0.0, by norm_num⟩, BlendMode.src, id, Filter.id) Full ) (Rect 0.0 0.0 1280.0 80.0) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Path 0) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 28.0 30.0 126.0 48.0)) ) (Path 1) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 28.0 30.0 126.0 48.0)) ) (saveLayer (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw empty (Path 2) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 3) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 4) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 5) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 6) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 7) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 8) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 9) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 10) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Path 11) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (saveLayer empty (draw empty (Path 12) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 49.0 30.0 126.0 48.0)) ) (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.custom LumaFilter) ) (Fill.pixel (Alpha 1), BlendMode.dstin, id, Filter.id) ) (Fill.pixel (Alpha 1), BlendMode.srcover, id, Filter.id) ) (TextBlob 153.84375 33.0 0.0 0.0 57.79945373535156 17.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 241.7967529296875 33.0 0.0 0.0 41.304656982421875 17.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 727.8907470703125 33.0 0.0 0.0 47.94537353515625 15.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 806.8597412109375 32.0 0.0 0.0 87.3359375 16.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 923.71875 33.0 0.0 0.0 52.57293701171875 15.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 1007.4337768554688 33.0 0.0 0.0 43.48956298828125 15.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (RRect 1090.0 16.0 1167.0 64.0 24.0 24.0 24.0 24.0) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 1105.4537353515625 32.0 0.0 0.0 45.9453125 19.0) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (RRect 1175.0 16.0 1264.0 64.0 24.0 24.0 24.0 24.0) (Fill.pixel ⟨1, 0.9137254901960784, 0.9137254901960784, 0.9137254901960784, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 1189.893798828125 32.0 0.0 0.0 59.1014404296875 19.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full )
  =
  denote (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw (draw empty Full (Fill.pixel ⟨0.0, 0.0, 0.0, 0.0, by norm_num⟩, BlendMode.src, id, Filter.id) Full ) (Rect 0.0 0.0 1280.0 80.0) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (Path 0) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 28.0 30.0 126.0 48.0)) ) (Path 1) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect Full (Rect 28.0 30.0 126.0 48.0)) ) (Path 2) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 3) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 4) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 5) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 6) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 7) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 8) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 9) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 10) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (Path 11) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) (intersect (intersect (intersect Full (Rect 49.0 30.0 126.0 48.0)) (Rect 49.27490234375 30.0 126.0000991821289 48.0)) (Rect 49.0 30.0 126.0 48.0)) ) (TextBlob 153.84375 33.0 0.0 0.0 57.79945373535156 17.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 241.7967529296875 33.0 0.0 0.0 41.304656982421875 17.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 727.8907470703125 33.0 0.0 0.0 47.94537353515625 15.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 806.8597412109375 32.0 0.0 0.0 87.3359375 16.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 923.71875 33.0 0.0 0.0 52.57293701171875 15.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 1007.4337768554688 33.0 0.0 0.0 43.48956298828125 15.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (RRect 1090.0 16.0 1167.0 64.0 24.0 24.0 24.0 24.0) (Fill.pixel ⟨1, 0.9019607843137255, 0.0, 0.13725490196078433, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 1105.4537353515625 32.0 0.0 0.0 45.9453125 19.0) (Fill.pixel ⟨1, 1.0, 1.0, 1.0, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (RRect 1175.0 16.0 1264.0 64.0 24.0 24.0 24.0 24.0) (Fill.pixel ⟨1, 0.9137254901960784, 0.9137254901960784, 0.9137254901960784, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full ) (TextBlob 1189.893798828125 32.0 0.0 0.0 59.1014404296875 19.0) (Fill.pixel ⟨1, 0.06666666666666667, 0.06666666666666667, 0.06666666666666667, by norm_num⟩, BlendMode.srcover, id, Filter.id) Full )
  :=
by
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  apply denote_in_draw
  grind [OpaqueSaveLayerRemoveLastDraw]
