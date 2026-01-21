open Classical

-- The basic indexing type
@[grind, simp]
def Point : Type := Unit

-- WTF IS TRANFORM DOING
-- IMO there are 2 spaces:
-- * the global coordinate set
-- * the local coordinate set
-- Remember a Layer maps a point to the
-- The transform matrix (multiplication is implicit)
@[grind, simp]
def Transform: Type := Point -> Point

-- Color := (red, green, blue, alpha)
@[grind, simp]
def Color : Type := (Float × Float × Float × Float)

@[grind, simp]
def isOpaque (c : Color) : Prop := c.2.2.2 = 1.0

example: isOpaque (1.0, 0.0, 0.0, 1.0) := by simp [isOpaque]

@[grind]
def Transparent : Color := (0.0, 0.0, 0.0, 0.0)

-- Geometry is a collection of points
abbrev Geometry := Point -> Bool

@[grind, simp]
def intersect (g1 g2 : Geometry) : Geometry :=
  fun pt => g1 pt && g2 pt

@[grind, simp]
def difference (g1 g2 : Geometry) : Geometry :=
  fun pt => g1 pt && not (g2 pt)

-- Style changes the geometry
abbrev Style := Geometry -> Geometry
@[grind, simp]
def Fill : Style := fun g => g

-- Color Filters
abbrev ColorFilter := Color -> Color
@[grind, simp]
def idColorFilter : ColorFilter := fun c => c
-- Paintdraw defines how a geometry is painted
abbrev PaintDraw := Style × (Point -> Color)

-- BlendMode blends 2 colors together
-- These area both easy and annoying to formally prove
-- so we are just going to leave them as axioms.
-- If you want to see the example formalization,
-- see Colors.lean.
abbrev BlendMode := Color -> Color -> Color

--  AXIOMS
--- SrcOver is a blend mode: r = s + (1-sa)*d
-- Can try to prove
axiom SrcOver : BlendMode
@[grind, simp]
axiom SrcOver_left_transparent:
  forall c : Color, SrcOver c Transparent = c
@[grind, simp]
axiom SrcOver_right_transparent :
  forall c : Color, SrcOver Transparent c = c
@[grind, simp]
axiom SrcOver_associative :
  forall c₁ c₂ c₃ : Color, SrcOver (SrcOver c₁ c₂) c₃ = SrcOver c₁ (SrcOver c₂ c₃)
axiom SrcOver_luminance_white:
  forall c (f: Color -> Color), f (1.0, 1.0, 1.0, 1.0) = (0.0, 0.0, 0.0, 1.0) -> f (SrcOver c (1.0, 1.0, 1.0, 1.0)) = SrcOver (f c) (0.0, 0.0, 0.0, 1.0)
@[grind, simp]
axiom SrcOver_right_opaque:
  forall c1 c2 : Color, isOpaque c2 -> SrcOver c1 c2 = c2

axiom DstIn: BlendMode
@[grind, simp]
axiom DstIn_left_transparent:
  forall c : Color, DstIn Transparent c = Transparent
@[grind, simp]
axiom DstIn_right_transparent:
  forall c : Color, DstIn c Transparent = Transparent
@[grind, simp]
axiom DstIn_right_opaque:
  forall c1 c2 : Color, isOpaque c2 -> DstIn c1 c2 = c1
@[simp]
axiom DstIn_right_opaque_general:
  forall (c : Color) (f : Point -> Color) (pt : Point),
    isOpaque (f pt) -> DstIn c (f pt) = c


-- blend mode src:
axiom Src : BlendMode
@[grind, simp]
axiom Src_def :
  forall c₁ c₂ : Color, Src c₁ c₂ = c₂

-- PaintBlend defines how 2 layers are blended together
abbrev PaintBlend := (Float × BlendMode × ColorFilter)

-- A layer is a buffer of pixels
abbrev Layer := Point -> Color

-- applyalpha applies an alpha across a layer
axiom applyAlpha : Float -> Color -> Color
@[grind, simp]
axiom applyAlpha_opaque :
  forall c : Color, applyAlpha 1.0 c = c
@[grind, simp]
axiom applyAlpha_transparent :
  forall c : Color, applyAlpha 0.0 c = Transparent
@[grind, simp]
axiom applyAlpha_on_transparent :
  forall a : Float, applyAlpha a Transparent = Transparent


@[grind, simp]
noncomputable def blend  (l₁ l₂ : Layer) (pb: PaintBlend) : Layer :=
  let (α, bm, cf) := pb
  fun pt => bm (l₁ pt) (applyAlpha α (cf (l₂ pt)))

  -- rasterizes a geometry into a layer
@[grind, simp]
noncomputable def raster (shape: Geometry) (paint: PaintDraw) (t: Transform) (clip: Geometry): Layer :=
  let (style, color) := paint
  fun pt =>
  let pt := (t pt)
  if (style shape) pt && (clip pt) then color pt else Transparent

-- Now we define layers
-- Empty()
@[grind, simp]
def EmptyLayer : Layer := (fun _ => Transparent)

-- SaveLayer blends a layer onto another layer
-- l₁ bottom layer
-- l₂ top layer
@[grind, simp]
noncomputable def SaveLayer (l₁ l₂ : Layer) (pb : PaintBlend) : Layer :=
  blend l₁ l₂ pb

--! REWRITE 1
@[grind, simp]
theorem empty_SrcOver_SaveLayer_is_Empty l:
  SaveLayer l EmptyLayer (1.0, SrcOver, idColorFilter) = l :=
  by grind

-- now we define draw
@[grind, simp]
noncomputable def Draw (l : Layer) (g : Geometry) (pd : PaintDraw) (pb : PaintBlend) (t: Transform)(clip : Geometry): Layer :=
  blend l (raster g pd t clip) pb

@[grind, simp]
theorem lone_draw_inside_opaque_srcover_savelayer
  (bottom : Layer) (g : Geometry) (pd : PaintDraw) (α: Float) (c : Geometry) (t: Transform) cf:
  SaveLayer bottom (Draw EmptyLayer g pd (α, SrcOver, cf) t c) (1.0, SrcOver, idColorFilter) = Draw bottom g pd (α, SrcOver, cf) t c :=
  by grind

--! REWRITE 2
@[grind, simp]
theorem lone_softlight_draw_inside_opaque_srcover_savelayer
  (g : Geometry) (pd : PaintDraw) (α: Float) (c : Geometry) (t: Transform) (any_bm: BlendMode) cf:
  SaveLayer EmptyLayer (Draw EmptyLayer g pd (α, any_bm, cf) t c) (1.0, SrcOver, id) = Draw EmptyLayer g pd (α, any_bm, cf) t c :=
  by grind

--! REWRITE 4
@[grind, simp]
theorem empty_src_is_noop g pd t c:
  Draw EmptyLayer g pd (0.0, Src, id) t c = EmptyLayer := by
  grind

--! REWRITE 3
@[grind, simp]
theorem last_draw_inside_opaque_srcover_savelayer
  (l₁ l₂ : Layer) (g c : Geometry) (pd : PaintDraw) (α : Float) (t : Transform) cf:
  SaveLayer l₁ (Draw l₂ g pd (α, SrcOver, cf) t c) (1.0, SrcOver, id) = Draw (SaveLayer l₁ l₂ (1.0, SrcOver, id)) g pd (α, SrcOver, cf) t c := by
  grind

--! REWRITE 5
@[grind, simp]
theorem dstin_into_clip g1 pd1 a1 c1 t g2 c2 c (H: isOpaque c):
  SaveLayer (Draw EmptyLayer g1 pd1 (a1, SrcOver, id) t c1)
  (Draw EmptyLayer g2 (Fill, fun _ => c) (1.0, SrcOver, id) t c2) (1.0, DstIn, id)
  =
  Draw EmptyLayer g1 pd1 (a1, SrcOver, id) t (intersect c1 (intersect g2 c2)) := by
  simp
  grind

@[grind]
inductive Clips (clip : Geometry) (t : Transform) : Layer -> Layer -> Prop where
| emptyClip : Clips clip t EmptyLayer EmptyLayer
| drawClip : forall l1 l2 g pd a c,
    Clips clip t l1 l2 ->
    Clips clip t (Draw l1 g pd (a, SrcOver, id) t c) (Draw l2 g pd (a, SrcOver, id) t (intersect c clip))

--! DSTIN
theorem dstin_into_clip2 t g2 c2 c (H: isOpaque c) bottom1 bottom2:
  Clips (intersect g2 c2) t bottom1 bottom2 ->
  SaveLayer bottom1
  (Draw EmptyLayer g2 (Fill, fun _ => c) (1.0, SrcOver, id) t c2) (1.0, DstIn, id)
  = bottom2 := by
  intro Hclip
  induction Hclip <;> simp at * <;> grind

theorem subsume_colorfilter g style c transform clip f (H: f Transparent = Transparent):
  SaveLayer EmptyLayer (Draw EmptyLayer g (style, fun _ => c) (1.0, SrcOver, id) transform clip)
                       (1.0, SrcOver, f) =
  Draw EmptyLayer g (style, fun _ => f c) (1.0, SrcOver, id) transform clip := by
  simp
  grind

theorem luma_to_diff_clip g1 g2 tfrm clip f (H1: f (0.0, 0.0, 0.0, 1.0) = f Transparent):
  SaveLayer EmptyLayer
            (Draw (Draw EmptyLayer g1 (id, fun _ => (1.0, 1.0, 1.0, 1.0)) (1.0, SrcOver, id) tfrm clip)
                  g2 (id, fun _ => (0.0, 0.0, 0.0, 1.0)) (1.0, SrcOver, id) tfrm clip)
            (1.0, SrcOver, f)
  =
  SaveLayer EmptyLayer
            (Draw EmptyLayer g1 (id, fun _ => (1.0, 1.0, 1.0, 1.0)) (1.0, SrcOver, id) tfrm (difference clip g2))
            (1.0, SrcOver, f) := by
  have H2 : SrcOver (1.0, 1.0, 1.0, 1.0) (0.0, 0.0, 0.0, 1.0) = (0.0, 0.0, 0.0, 1.0) := by grind
  simp
  grind

theorem luma_to_diff_clip2 l g1 g2 tfrm clip f (H1: f (0.0, 0.0, 0.0, 1.0) = f Transparent):
  SaveLayer l
            (Draw (Draw EmptyLayer g1 (id, fun _ => (1.0, 1.0, 1.0, 1.0)) (1.0, SrcOver, id) tfrm clip)
                  g2 (id, fun _ => (0.0, 0.0, 0.0, 1.0)) (1.0, SrcOver, id) tfrm clip)
            (1.0, SrcOver, f)
  =
  SaveLayer l
            (Draw EmptyLayer g1 (id, fun _ => (1.0, 1.0, 1.0, 1.0)) (1.0, SrcOver, id) tfrm (difference clip g2))
            (1.0, SrcOver, f) := by
  have H2 : SrcOver (1.0, 1.0, 1.0, 1.0) (0.0, 0.0, 0.0, 1.0) = (0.0, 0.0, 0.0, 1.0) := by grind
  simp
  grind

theorem dstin_masks shape style color tfrm clip gradient
        (Hopaque : forall pt, isOpaque (gradient pt)):
  SaveLayer (Draw (EmptyLayer) shape (style, fun _ => color) (1.0, SrcOver, id) tfrm clip)
            (Draw (EmptyLayer) shape (style, gradient) (1.0, SrcOver, id) tfrm clip)
            (1.0, DstIn, id)
  =
  Draw (EmptyLayer) shape (style, fun _ => color) (1.0, SrcOver, id) tfrm clip := by
  grind

-- this
theorem textblob_mask
  (shape shape': Geometry) (color color' : Color)
  (transform : Transform) (clip : Geometry)
  (Hopaque : isOpaque color') :
  SaveLayer (Draw EmptyLayer shape (id, fun _ => color) (1.0, SrcOver, id) transform clip)
            (Draw EmptyLayer shape' (id, fun _ => color') (1.0, SrcOver, id) transform clip)
            (1.0, DstIn, id)
    =
  Draw EmptyLayer shape' (id, fun _ => color) (1.0, SrcOver, id) transform (intersect clip shape) :=
by
  simp
  grind
