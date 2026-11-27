/- GID: D5/S3/Topology/OrdinaryCollarRetraction
   generality: G
   mirror-B: D5/B/S3/Topology/OrdinaryCollarRetraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Two colour cuts give an actual retraction with exact selected support. -/

import D5.S3.Topology.OrdinarySubdivisionMap

/-! Realize the two-cut image as a point of the actual subdivided colour
subcomplex. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.OrdinaryCollarRetraction

open BarycentricGraphDistance (Face)
open BarycentricBaseRigidity (sd)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open GraphSubdivisionIntervals (originalSupport)
open OrdinarySubdivisionMap (cutFace cutFlag inTwoCutCollar twoCutImage mem_twoCutImage_support)

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {X : Type} {K : PreAbstractSimplicialComplex X}

/-- The full subcomplex on the selected old vertices. -/
def colourComplex (K : PreAbstractSimplicialComplex X) (colour : X → Bool) :
    PreAbstractSimplicialComplex X where
  faces := {s | s ∈ K ∧ ∀ x ∈ s, colour x = true}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(K.isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts hne
    exact ⟨(K.isRelLowerSet_faces hs.1).2 hts hne, fun x hx => hs.2 x (hts hx)⟩

private def first (colour : X → Bool) :
    {a : Face K // (cutFace colour a).Nonempty} →o Face (colourComplex K colour) where
  toFun a := ⟨cutFace colour a.val,
    (K.isRelLowerSet_faces a.val.property).2 (Finset.filter_subset _ _) a.property,
    fun _ hx => (Finset.mem_filter.mp hx).2⟩
  monotone' := fun _ _ h => Finset.filter_subset_filter _ h

private theorem chain_image {P Q : Type*} [Preorder P] [PartialOrder Q]
    {p : P → Prop} [DecidablePred p] (f : Subtype p →o Q) (s : Finset P)
    (hchain : IsChain (· < ·) (s : Set P)) :
    IsChain (· < ·) (↑((s.subtype p).image f) : Set Q) := by
  intro u hu v hv hne
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  have hab : a.val ≠ b.val := fun h => hne (congrArg f (Subtype.ext h))
  rcases hchain (Finset.mem_subtype.mp ha) (Finset.mem_subtype.mp hb) hab with h | h
  · exact Or.inl (lt_of_le_of_ne (f.monotone h.le) hne)
  · exact Or.inr (lt_of_le_of_ne (f.monotone h.le) hne.symm)

private theorem cutFlag_nonempty (colour : X → Bool) (b : Face (sd K)) :
    (cutFlag colour b).Nonempty ↔ ∃ a ∈ b.val, (cutFace colour a).Nonempty := by
  unfold cutFlag
  rw [Finset.image_nonempty]
  simp only [Finset.Nonempty, Finset.mem_filter]
  rfl

private def second (colour : X → Bool) :
    {b : Face (sd K) // (cutFlag colour b).Nonempty} →o Face (sd (colourComplex K colour)) where
  toFun b := by
    let s := b.val.val
    let p := fun a : Face K => (cutFace colour a).Nonempty
    have hne : (s.subtype p).Nonempty := by
      obtain ⟨a, ha, h⟩ := (cutFlag_nonempty colour b.val).mp b.property
      exact ⟨⟨a, h⟩, Finset.mem_subtype.mpr ha⟩
    refine ⟨(s.subtype p).image (first colour), hne.image _,
      chain_image (p := p) (first colour) s b.val.property.2.1, fun z _ => z.property⟩
  monotone' := fun _ _ h => Finset.image_subset_image (Finset.subtype_mono h)

private theorem second_image (colour : X → Bool)
    (b : {b : Face (sd K) // (cutFlag colour b).Nonempty}) :
    (((second colour) b).val.image fun a => a.val) = cutFlag colour b.val := by
  ext s
  change s ∈ ((b.val.val.subtype fun a => (cutFace colour a).Nonempty).image
    (first colour)).image Subtype.val ↔ s ∈ cutFlag colour b.val
  rw [Finset.image_image, cutFlag]
  simp only [Finset.mem_image, Finset.mem_subtype, Function.comp_apply, Finset.mem_filter]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ⟨ha, a.property⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
    exact ⟨⟨a, hp⟩, ha, rfl⟩

/-- The two-cut collar retracts at the level of third-subdivision vertices
by an inclusion-preserving map into the subdivided colour complex. -/
def retract (colour : X → Bool) :
    {v : Face (sd (sd K)) // inTwoCutCollar colour v} →o
      Face (sd (sd (colourComplex K colour))) where
  toFun v := by
    let p := fun b : Face (sd K) => (cutFlag colour b).Nonempty
    have hn : (v.val.val.subtype p).Nonempty := by
      obtain ⟨b, hb⟩ := v.val.property.1
      exact ⟨⟨b, v.property b hb⟩, Finset.mem_subtype.mpr hb⟩
    refine ⟨(v.val.val.subtype p).image (second colour), hn.image _,
      chain_image (p := p) (second colour) _ v.val.property.2.1, fun z _ => z.property⟩
  monotone' := fun _ _ h => Finset.image_subset_image (Finset.subtype_mono h)

/-- Forgetting the face membership proofs in the actual retraction gives
the nested image of the two ordinary cuts. -/
theorem retract_image (colour : X → Bool)
    (v : {v : Face (sd (sd K)) // inTwoCutCollar colour v}) :
    ((retract colour v).val.image fun b => b.val.image fun a => a.val) =
      twoCutImage colour v.val := by
  ext s
  change s ∈ ((v.val.val.subtype fun b => (cutFlag colour b).Nonempty).image
    (second colour)).image (fun b => b.val.image Subtype.val) ↔ s ∈ twoCutImage colour v.val
  rw [Finset.image_image, twoCutImage]
  simp only [Finset.mem_image, Finset.mem_subtype, Function.comp_apply, second_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.val, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, v.property b hb⟩, hb, rfl⟩

private theorem mem_originalSupport_three (v : Face (sd (sd K))) (x : X) :
    x ∈ originalSupport K 3 {v} ↔ ∃ b ∈ v.val, ∃ a ∈ b.val, x ∈ a.val := by
  let p (b : Face (sd K)) : Finset (Face K) := b.val
  let q (a : Face K) : Finset X := a.val
  let top (w : Face (sd (sd K))) : Finset (Face (sd K)) := w.val
  change x ∈ ((({v} : Finset _).biUnion top).biUnion p).biUnion q ↔ _
  simp only [Finset.singleton_biUnion, Finset.mem_biUnion]
  exact ⟨fun ⟨a, ⟨b, hb, ha⟩, h⟩ => ⟨b, hb, a, ha, h⟩,
    fun ⟨b, hb, a, ha, h⟩ => ⟨a, ⟨b, hb, ha⟩, h⟩⟩

/-- The actual retracted vertex has exactly the selected old support. -/
theorem retract_support (colour : X → Bool)
    (v : {v : Face (sd (sd K)) // inTwoCutCollar colour v}) :
    originalSupport (colourComplex K colour) 3 {retract colour v} =
      (originalSupport K 3 {v.val}).filter fun x => colour x = true := by
  ext x
  rw [Finset.mem_filter, ← mem_twoCutImage_support, ← retract_image colour v,
    mem_originalSupport_three]
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨b, hb, a, ha, hx⟩
    exact ⟨_, Finset.mem_image.mpr ⟨b, hb, rfl⟩, _, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hx⟩
  · rintro ⟨b', hb', a', ha', hx⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    exact ⟨b, hb, a, ha, hx⟩

end

end D5.S3.Topology.OrdinaryCollarRetraction
