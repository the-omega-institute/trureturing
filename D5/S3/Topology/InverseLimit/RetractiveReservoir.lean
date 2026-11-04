/- GID: D5/S3/Topology/InverseLimit/RetractiveReservoir
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/RetractiveReservoir
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proper-stage compact attachment reservoirs force actual final transverse sequences. -/

import D5.S3.Topology.Resolution.RetractiveAttachment
import D5.S3.Topology.InverseLimit.CompactRangePersistence

/-!
Direct consumed application of compact natural-range persistence to the
literal retractive attachment topology. The final carrier uses the actual
coherent-thread core and components, with the actual induced attachment maps.
There is no assumption of final-range membership or onto fibre restrictions.
The index category can be the opposite of any nonempty ordinal prefix, of
arbitrary cofinality; the proof uses cofiltered compactness, not a cofinal
sequence. No irreducibility of the prefix is asserted. Original KPI 0.
-/

open CategoryTheory Set Function Filter Topology

namespace D5.S3.Topology.InverseLimit.RetractiveReservoir

open CompactRangePersistence
open D5.S3.Topology.Resolution.RetractiveAttachment

universe u v w

/-- A fixed infinite family of ranges through one actual proper-stage core
thread survives in the actual final component ranges and supplies an actual
convergent injective sequence in the final attachment carrier. -/
theorem persistent_reservoir_sequence
    {J : Type u} [SmallCategory J] [IsCofilteredOrEmpty J] {I : Type w}
    (G : J ⥤ TopCat.{max u v}) (F : I → J ⥤ TopCat.{max u v})
    (t : ∀ i, F i ⟶ G)
    [∀ i j, CompactSpace ((F i).obj j)] [∀ i j, T2Space ((F i).obj j)]
    [∀ j, T2Space (G.obj j)]
    (b : (TopCat.limitCone G).pt) (R : Set I) (hR : R.Infinite)
    (hb : ∀ i ∈ R, ∀ j, b.val j ∈ range ((t i).app j)) :
    (∀ i ∈ R, b ∈ range (limitMap (F i) G (t i))) ∧
    ∃ x : ℕ → Space (fun i => limitMap (F i) G (t i)),
      Injective x ∧ Tendsto x atTop (𝓝 (core (fun i => limitMap (F i) G (t i)) b)) ∧
      ∀ n, x n ≠ core (fun i => limitMap (F i) G (t i)) b := by
  have hr : ∀ i ∈ R, b ∈ range (limitMap (F i) G (t i)) :=
    fun i hi => mem_range_limit_map (F i) G (t i) b (hb i hi)
  refine ⟨hr,?_⟩
  apply sequence_of_infinite_multiplicity (fun i => limitMap (F i) G (t i))
    (fun i => (limitMap (F i) G (t i)).continuous) b
  exact hR.mono hr

end D5.S3.Topology.InverseLimit.RetractiveReservoir
