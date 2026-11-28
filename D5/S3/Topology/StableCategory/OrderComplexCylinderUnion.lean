/- GID: D5/S3/Topology/StableCategory/OrderComplexCylinderUnion
   generality: I
   mirror-B: none(waiver:consumed-by-weak-category-one-reduction)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lower amalgamations give exact unions of order complexes. -/

import D5.S3.Topology.StableCategory.OrderComplexNullhomotopy
import D5.S3.Topology.StableCategory.PosetMappingCylinderGlue

noncomputable section

open Set
open D5.S3.Topology.OrderComplexNullhomotopy (orderComplex)
open D5.S3.Topology.PosetMappingCylinderGlue

namespace D5.S3.Topology.OrderComplexCylinderUnion

private theorem mem_map_orderComplex_iff {X Y : Type} [PartialOrder X] [PartialOrder Y]
    [Fintype X] [DecidableEq Y] (e : X ↪o Y) (s : Finset Y) :
    s ∈ (orderComplex X).map e ↔ s ∈ orderComplex Y ∧ (s : Set Y) ⊆ Set.range e := by
  classical
  change (∃ t : Finset X, t ∈ orderComplex X ∧ t.image e = s) ↔ _
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨Finset.image_nonempty.mpr ht.1, ?_⟩, Finset.coe_image_subset_range⟩
    rw [Finset.coe_image]
    exact IsChain.image_embedding_iff.mpr ht.2
  · rintro ⟨hs, hrange⟩
    have hsub : s ⊆ Finset.univ.image e := by
      intro y hy
      obtain ⟨x, rfl⟩ := hrange hy
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    obtain ⟨t, _, rfl⟩ := Finset.subset_image_iff.mp hsub
    refine ⟨t, ⟨Finset.image_nonempty.mp hs.1, ?_⟩, rfl⟩
    apply IsChain.image_embedding_iff (φ := e) |>.mp
    simpa only [← Finset.coe_image] using hs.2

variable {R A V : Type} [PartialOrder R] [PartialOrder A] [PartialOrder V]
    [Fintype R] [Fintype A] [Fintype V]
variable (u : R →o A) (e : R ↪o V) (he : IsLowerSet (Set.range (e : R → V)))

local instance : DecidableEq (Glue u e he) := Classical.decEq _

/-- The order complex of the amalgam is the union of the two embedded order
complexes, with intersection precisely the embedded common lower subposet. -/
theorem orderComplex_glue :
    orderComplex (Glue u e he) = (orderComplex V).map (inV u e he) ⊔
      (orderComplex (Cylinder u)).map (inCylinder u e he) ∧
    (orderComplex V).map (inV u e he) ⊓
      (orderComplex (Cylinder u)).map (inCylinder u e he) =
        (orderComplex R).map (e.comp (inV u e he)) := by
  constructor
  · apply SetLike.ext
    intro s
    change s ∈ orderComplex (Glue u e he) ↔
      s ∈ (orderComplex V).map (inV u e he) ∨
        s ∈ (orderComplex (Cylinder u)).map (inCylinder u e he)
    rw [mem_map_orderComplex_iff, mem_map_orderComplex_iff]
    constructor
    · intro hs
      rcases chain_subset_range u e he hs.2 with hV | hC
      · exact Or.inl ⟨hs, hV⟩
      · exact Or.inr ⟨hs, hC⟩
    · rintro (h | h) <;> exact h.1
  · apply SetLike.ext
    intro s
    change (s ∈ (orderComplex V).map (inV u e he) ∧
      s ∈ (orderComplex (Cylinder u)).map (inCylinder u e he)) ↔ _
    rw [mem_map_orderComplex_iff, mem_map_orderComplex_iff, mem_map_orderComplex_iff,
      ← range_inV_inter_range_inCylinder u e he]
    constructor
    · rintro ⟨⟨hs, hV⟩, _, hC⟩
      exact ⟨hs, fun _ ht => ⟨hV ht, hC ht⟩⟩
    · rintro ⟨hs, ht⟩
      exact ⟨⟨hs, fun _ h => (ht h).1⟩, ⟨hs, fun _ h => (ht h).2⟩⟩

end D5.S3.Topology.OrderComplexCylinderUnion
