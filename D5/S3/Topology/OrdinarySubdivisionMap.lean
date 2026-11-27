/- GID: D5/S3/Topology/OrdinarySubdivisionMap
   generality: G
   mirror-B: D5/B/S3/Topology/OrdinarySubdivisionMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Colour cuts and old supports commute with ordinary subdivision of a simplicial map. -/

import D5.S3.Topology.GraphSubdivisionIntervals
import Mathlib.Data.Finset.Union

/-! Old supports under the ordinary subdivision of a simplicial vertex map.
The map can identify vertices, as in the projection to a rank-coloured
tetrahedron and the fold to a triangle cone in Question 6.3. -/

namespace D5.S3.Topology.OrdinarySubdivisionMap

open BarycentricGraphDistance (Face)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open BarycentricBaseRigidity (sd)
open GraphSubdivisionIntervals (originalSupport)

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X Y : Type} {K : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}

private abbrev image {A B : Type} (s : Finset A) (f : A → B) : Finset B :=
  @Finset.image A B (Classical.decEq B) f s

private def faceOrderMap (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L) : Face K →o Face L where
  toFun s := ⟨image s.val f, hf _ s.property⟩
  monotone' := fun _ _ h => Finset.image_subset_image h

private theorem image_subdivision_face (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    {s : Finset (Face K)} (hs : s ∈ sd K) :
    image s (faceOrderMap f hf) ∈ sd L := by
  let _ : DecidableEq (Face L) := Classical.decEq _
  unfold image
  refine ⟨hs.1.image _, ?_, fun q _ => q.property⟩
  intro a ha b hb hab
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  rcases hs.2.1 hu hv (fun h => hab (congrArg (faceOrderMap f hf) h)) with h | h
  · exact Or.inl (lt_of_le_of_ne ((faceOrderMap f hf).monotone h.le) hab)
  · exact Or.inr (lt_of_le_of_ne ((faceOrderMap f hf).monotone h.le) hab.symm)

/-- Each successive vertex maps to the image of its nonempty flag. -/
def iterate (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L) :
    (n : ℕ) → {g : (iteratedAmbient K n).1 → (iteratedAmbient L n).1 //
      ∀ s ∈ (iteratedAmbient K n).2, image s g ∈ (iteratedAmbient L n).2}
  | 0 => ⟨f, hf⟩
  | n + 1 => by
      let g := iterate f hf n
      let step := faceOrderMap (K := (iteratedAmbient K n).2)
        (L := (iteratedAmbient L n).2) g.val g.property
      refine ⟨step, fun s hs => ?_⟩
      exact image_subdivision_face (K := (iteratedAmbient K n).2)
        (L := (iteratedAmbient L n).2) g.val g.property hs

/-- The original support of a subdivided image is the image of its old
support. In particular, a colour meeting the old support can be read
after mapping to the coloured chamber. -/
theorem originalSupport_image (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (n : ℕ) (s : Finset (iteratedAmbient K n).1) :
    originalSupport L n (image s (iterate f hf n).val) =
      image (originalSupport K n s) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let g := iterate f hf n
    let s' : Finset (Face (iteratedAmbient K n).2) := s
    let source (x : Face (iteratedAmbient K n).2) : Finset (iteratedAmbient K n).1 := x.val
    let target (y : Face (iteratedAmbient L n).2) : Finset (iteratedAmbient L n).1 := y.val
    let step := faceOrderMap (K := (iteratedAmbient K n).2)
      (L := (iteratedAmbient L n).2) g.val g.property
    change originalSupport L n ((image s' step).biUnion target) =
      image (originalSupport K n (s'.biUnion source)) f
    have h :
        (image s' step).biUnion target =
          image (s'.biUnion source) g.val := by
      let _ : DecidableEq (Face (iteratedAmbient L n).2) := Classical.decEq _
      unfold image
      rw [Finset.image_biUnion, Finset.biUnion_image]
      rfl
    rw [h]
    exact ih (s'.biUnion source)


/-- If the original map is injective on the vertices of a subcomplex,
every ordinary subdivision remains injective on that subdivided
subcomplex. The map may identify vertices elsewhere. -/
theorem iterate_injOn_subcomplex (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (P : PreAbstractSimplicialComplex X) (hinj : Set.InjOn f {x | {x} ∈ P}) (n : ℕ) :
    Set.InjOn (iterate f hf n).val
      {x | {x} ∈ BarycentricNeighborhoodIteration.iteratedSubcomplex K P n} := by
  induction n with
  | zero => exact hinj
  | succ n ih =>
    let Q := BarycentricNeighborhoodIteration.iteratedSubcomplex K P n
    intro a ha b hb he
    have haQ : a.val ∈ Q := ha.2.2 a (Finset.mem_singleton_self a)
    have hbQ : b.val ∈ Q := hb.2.2 b (Finset.mem_singleton_self b)
    have vertices {s : Finset (iteratedAmbient K n).1} (hs : s ∈ Q) :
        (s : Set (iteratedAmbient K n).1) ⊆ {x | {x} ∈ Q} := by
      intro x hx
      exact (Q.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty x)
    have himage : image a.val (iterate f hf n).val = image b.val (iterate f hf n).val :=
      congrArg (fun q : Face (iteratedAmbient L n).2 => q.val) he
    have reflect {s t : Finset (iteratedAmbient K n).1} (hs : s ∈ Q) (ht : t ∈ Q)
        (heq : image s (iterate f hf n).val = image t (iterate f hf n).val) : s ⊆ t := by
      intro x hx
      have hmem : (iterate f hf n).val x ∈ image t (iterate f hf n).val :=
        heq ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, eq⟩ := Finset.mem_image.mp hmem
      have := ih (vertices ht hy) (vertices hs hx) eq
      simpa only [this] using hy
    exact Subtype.ext (Finset.Subset.antisymm (reflect haQ hbQ himage)
      (reflect hbQ haQ himage.symm))

section Cuts

set_option backward.isDefEq.respectTransparency false

/-- Intersect an old face with the selected colour. -/
def cutFace (colour : X → Bool) (a : Face K) : Finset X :=
  a.val.filter (colour · = true)

/-- Keep the nonempty intersections in a flag, identifying repetitions. -/
def cutFlag (colour : X → Bool) (b : Face (iteratedAmbient K 1).2) :
    Finset (Finset X) :=
  (b.val.filter fun a => (cutFace colour a).Nonempty).image (cutFace colour)

/-- After the two cuts, the ordinary third subdivision retains a flag
when all its constituent second-level vertices survive. -/
def inTwoCutCollar (colour : X → Bool) (v : Face (iteratedAmbient K 2).2) : Prop :=
  ∀ b ∈ v.val, (cutFlag colour b).Nonempty


/-- The third-level retraction as nested nonempty flags on the selected colour.
Outside the collar, some of the inner flags can be empty. -/
def twoCutImage (colour : X → Bool) (v : Face (iteratedAmbient K 2).2) :
    Finset (Finset (Finset X)) :=
  v.val.image (cutFlag colour)


/-- The actual two cuts retain exactly the chosen colour in the original
support. Discarding empty flags and identifying equal flags lose no
original vertices of that colour. -/
theorem mem_twoCutImage_support (colour : X → Bool)
    (v : Face (iteratedAmbient K 2).2) (x : X) :
    x ∈ (twoCutImage colour v).biUnion (fun b => b.biUnion id) ↔
      x ∈ originalSupport K 3 {v} ∧ colour x = true := by
  have h :
      x ∈ originalSupport K 3 {v} ↔ ∃ b ∈ v.val, ∃ a ∈ b.val, x ∈ a.val := by
    let _ : DecidableEq X := Classical.decEq _
    let _ : DecidableEq (Face K) := Classical.decEq _
    let _ : DecidableEq (Face (iteratedAmbient K 1).2) := Classical.decEq _
    let p (b : Face (iteratedAmbient K 1).2) : Finset (Face K) := b.val
    let q (a : Face K) : Finset X := a.val
    let start (w : Face (iteratedAmbient K 2).2) : Finset (Face (iteratedAmbient K 1).2) :=
      w.val
    change x ∈ ((({v} : Finset _).biUnion start).biUnion p).biUnion q ↔ _
    rw [Finset.singleton_biUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, ha, hx⟩
      obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
      exact ⟨b, hb, a, ha, hx⟩
    · rintro ⟨b, hb, a, ha, hx⟩
      exact ⟨a, Finset.mem_biUnion.mpr ⟨b, hb, ha⟩, hx⟩
  rw [h]
  simp only [twoCutImage, Finset.mem_biUnion]
  constructor
  · rintro ⟨B, hB, A, hA, hx⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨ha', _⟩ := Finset.mem_filter.mp ha
    obtain ⟨hx', hc⟩ := Finset.mem_filter.mp (show x ∈ cutFace colour a from hx)
    exact ⟨⟨b, hb, a, ha', hx'⟩, hc⟩
  · rintro ⟨⟨b, hb, a, ha, hx⟩, hc⟩
    have hcut : x ∈ cutFace colour a := Finset.mem_filter.mpr ⟨hx, hc⟩
    exact ⟨cutFlag colour b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      cutFace colour a, Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, ⟨x, hcut⟩⟩, rfl⟩,
      hcut⟩

variable (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
  (colour : X → Bool) (targetColour : Y → Bool)
  (hcolour : ∀ x, targetColour (f x) = colour x)

include hcolour

private theorem cutFace_image (a : Face K) :
    cutFace targetColour ((iterate f hf 1).val a) = image (cutFace colour a) f := by
  change ((image a.val f).filter (targetColour · = true)) = image (cutFace colour a) f
  unfold cutFace image
  rw [Finset.filter_image]
  simp only [hcolour]

private theorem cutFlag_image (b : Face (iteratedAmbient K 1).2) :
    cutFlag targetColour ((iterate f hf 2).val b) =
      image (cutFlag colour b) (fun a => image a f) := by
  let g : Face K → Face L := (iterate f hf 1).val
  change ((image b.val g).filter fun a => (cutFace targetColour a).Nonempty).image
    (cutFace targetColour) = image (cutFlag colour b) (fun a => image a f)
  unfold cutFlag image
  rw [Finset.filter_image, Finset.image_image, Finset.image_image]
  simp only [Function.comp_def, g, cutFace_image f hf colour targetColour hcolour, image,
    Finset.image_nonempty]
  rfl

/-- A colour-preserving simplicial map detects collar membership even when
it identifies vertices. -/
theorem inTwoCutCollar_iterate_iff (v : Face (iteratedAmbient K 2).2) :
    inTwoCutCollar targetColour ((iterate f hf 3).val v) ↔ inTwoCutCollar colour v := by
  let g : Face (iteratedAmbient K 1).2 → Face (iteratedAmbient L 1).2 :=
    (iterate f hf 2).val
  change (∀ b ∈ image v.val g, (cutFlag targetColour b).Nonempty) ↔ _
  unfold inTwoCutCollar
  constructor
  · intro h b hb
    simpa only [g, cutFlag_image f hf colour targetColour hcolour, image, Finset.image_nonempty]
      using h (g b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    simpa only [g, cutFlag_image f hf colour targetColour hcolour, image, Finset.image_nonempty]
      using h a ha

/-- The two cuts and final flag image commute with any colour-preserving
simplicial vertex map. In particular a balanced colouring gives the same
retraction in every chamber containing a subdivided face. -/
theorem twoCutImage_iterate (v : Face (iteratedAmbient K 2).2) :
    twoCutImage targetColour ((iterate f hf 3).val v) =
      image (twoCutImage colour v) (fun b => image b (fun a => image a f)) := by
  let g : Face (iteratedAmbient K 1).2 → Face (iteratedAmbient L 1).2 :=
    (iterate f hf 2).val
  change (image v.val g).image (cutFlag targetColour) = _
  unfold twoCutImage image
  rw [Finset.image_image, Finset.image_image]
  simp only [Function.comp_def, g, cutFlag_image f hf colour targetColour hcolour, image]
  rfl

end Cuts

end

end D5.S3.Topology.OrdinarySubdivisionMap
