import LambdaSkia.Colors

open Pixel

@[grind, simp]
def Point : Type := Unit

@[grind, simp]
def Geometry : Type := Unit -> Bool

@[grind, simp]
def Fill : Type := Point -> Pixel

@[grind, simp]
def BlendMode : Type := Pixel -> Pixel -> Pixel

@[grind, simp]
def Style : Type := Geometry -> Geometry

@[grind, simp]
def Filter : Type := Pixel -> Pixel

@[grind, simp]
def Paint : Type := Fill × BlendMode × Style × Filter

@[grind]
structure SavePaint where
  paint : Paint
  constPixel : Pixel
  fill_const : ∀ pt : Point, paint.1 pt = constPixel

@[simp] lemma SavePaint.alpha_bounds (p : SavePaint) :
  0 <= p.constPixel.a ∧ p.constPixel.a <= 1 :=
by
  -- p.constPixel.valid : 0 <= a ∧ a <= 1 ∧ ...
  exact ⟨p.constPixel.valid.1, p.constPixel.valid.2.1⟩

@[grind, simp]
def mk_save_paint
  (blend : BlendMode)
  (filter : Filter)
  (alpha : Real)
  (H : 0 <= alpha ∧ alpha <= 1) : SavePaint :=
  let c := Pixel.AlphaPixel alpha H
{
    paint := ((fun _ : Point => c), blend, id, filter),
    constPixel := c,
    fill_const := by grind
}

instance : Coe SavePaint Paint where
  coe sp := sp.paint

def getAlpha (p : SavePaint) : Real :=
  p.constPixel.a

@[grind]
inductive Layer : Type where
  | empty : Layer
  | draw  : Layer -> Geometry -> Paint -> Geometry -> Layer
  | saveLayer  : Layer -> Layer -> SavePaint -> Layer

open Layer

@[grind, simp]
def denote : Layer -> Point -> Pixel
  | empty, _ => Pixel.Transparent
  | draw l_b geo paint clip, pt =>
    let l_b := denote l_b
    let (fill, blend_mode, style, filter) := paint
    let drawPx := if (style geo) pt && (clip pt) then fill pt else Pixel.Transparent
    blend_mode (l_b pt) (filter drawPx)
    | saveLayer l_b l_t sp, pt =>
    let l_b := denote l_b
    let l_t := denote l_t
    let blend_mode : BlendMode := sp.paint.2.1
    let filter     : Filter    := sp.paint.2.2.2
    blend_mode (l_b pt) (filter (applyAlpha sp.constPixel.a (SavePaint.alpha_bounds sp) (l_t pt)))

notation "⟦" l "⟧" => denote l

theorem OpaqueSaveLayerEmptyLayer l_b :
  denote (saveLayer l_b
                    empty
                    (mk_save_paint srcover id 1 ⟨by norm_num, by norm_num⟩))
  =
  denote l_b :=
by
  ext pt
  simp

theorem OpaqueSaveLayerRemoveLoneDraw
  (g : Geometry)
  (paint : Paint)
  (clip : Geometry) :
  denote (saveLayer empty
                    (draw empty g paint clip)
                    (mk_save_paint srcover id 1 ⟨by norm_num, by norm_num⟩))
  =
  denote (draw empty g paint clip) :=
by
  ext pt
  simp

theorem OpaqueSaveLayerRemoveLastDraw
  (l₁ l₂ : Layer)
  (g clip : Geometry)
  (fill : Fill)
  (style : Style)
  (filter : Filter) :
  denote
    (saveLayer l₁
      (draw l₂ g (fill, srcover, style, filter) clip)
      (mk_save_paint srcover id 1 ⟨by norm_num, by norm_num⟩))
  =
  denote
    (draw
      (saveLayer l₁ l₂ (mk_save_paint srcover id 1 ⟨by norm_num, by norm_num⟩))
      g (fill, srcover, style, filter) clip) :=
by
  ext pt
  simp
  grind

theorem SubsumeColorFilter
  (g clip : Geometry)
  (style : Style)
  (c : Pixel)
  (f : Filter)
  (H : f Transparent = Transparent) :
  denote
    (saveLayer empty
      (draw empty g ((fun _ => c), srcover, style, id) clip)
      (mk_save_paint srcover f 1 ⟨by norm_num, by norm_num⟩))
  =
  denote
    (draw empty g ((fun _ => f c), srcover, style, id) clip) :=
by
  ext pt
  simp [denote]
  grind

theorem better_masks
  (shape clip1 clip2 : Geometry)
  (style : Style)
  (color : Pixel)
  (gradient : Fill)
  (Hsubset : ∀ pt, clip1 pt = true → clip2 pt = true)
  (Hopaque : ∀ pt, (gradient pt).a = 1) :
  denote
    (saveLayer
      (draw empty shape ((fun _ => color), srcover, style, id) clip1)
      (draw empty shape (gradient, srcover, style, id) clip2)
      (mk_save_paint dstin id 1 ⟨by norm_num, by norm_num⟩))
  =
  denote (draw empty shape ((fun _ => color), srcover, style, id) clip1) :=
by
  ext pt
  simp [denote]
  grind

/- @[grind]
inductive DrawOnly : Layer → Type where
| empty : DrawOnly Layer.empty
| draw  :
    ∀ (g : Geometry) (fill : Fill) (style : Style) (clip : Geometry) (l : Layer),
    DrawOnly l →
    DrawOnly (Layer.draw l g (fill, srcover, style, id) clip)

@[grind, simp]
def mask
  (m : Geometry)
  : ∀ {l : Layer}, DrawOnly l → Layer
  | _, DrawOnly.empty =>
      Layer.empty
  | _, @DrawOnly.draw g fill style clip _ h =>
      Layer.draw
        (mask m h)
        g
        (fill, srcover, style, id)
        (fun pt => clip pt && m pt)


theorem MaskIntoDstin
  (bottom : Layer)
  (Hdraw : DrawOnly bottom)
  (shape clip : Geometry)
  (c : Pixel)
  (Hopaque : c.a = 1) :
  denote
    (saveLayer
      bottom
      (draw empty shape ((fun _ => c), srcover, id, id) clip)
      (mk_save_paint dstin id 1 ⟨by norm_num, by norm_num⟩))
  =
  denote
    (mask (fun pt => shape pt && clip pt) Hdraw) :=
by
  ext pt
  simp [denote]
  grind
 -/
