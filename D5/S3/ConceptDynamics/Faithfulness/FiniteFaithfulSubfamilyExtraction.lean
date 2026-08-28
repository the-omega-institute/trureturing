/- GID: D5/S3/ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A faithful observer family on a finite state carrier has a faithful finite subfamily. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Lattice

/- Library-search audit trail (2026-08-26):
   * Exact D5 primitive hit `jointReadout` is the canonical dependent product
     of the source observer family and is used for both full and selected
     readouts; no second family readout is introduced.
   * `FiniteCoverCounting.finite_cover_laws` extracts a target-relative
     Fin-indexed sufficient family behind a baseline and range factorization,
     not a finite subset with an injective restricted joint readout.
   * `FiniteInterventionExtraction.finite_intervention_extraction` assumes a
     common response carrier and `Fin n`, so it is not exact for the dependent
     output family and arbitrary finite carrier here.
   * Body-shape searches for a finite selected `jointReadout` under full-family
     injectivity found no whole D5 theorem. Exact pinned-Mathlib hit
     `Set.finite_subset_iUnion` performs the finite extraction and is applied
     directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.FiniteFaithfulSubfamilyExtraction

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- If all coordinates jointly distinguish a finite state carrier, finitely
many coordinates already distinguish it. Selected outputs retain their
original dependent carriers. -/
theorem finite_faithful_subfamily_extraction
    {X : Type u} {Index : Type v} {Output : Index -> Type w} [Finite X]
    (readout : forall index, X -> Output index)
    (fullFaithful : Function.Injective (jointReadout readout)) :
    exists selected : Finset Index,
      Function.Injective
        (jointReadout
          (fun index : {candidate // candidate ∈ selected} =>
            readout index.1)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (X × X) := inferInstance
  let pairUniverse : Set (X × X) := {pair | pair.1 ≠ pair.2}
  let separatedBy (index : Index) : Set (X × X) :=
    {pair | pair.1 ≠ pair.2 ∧ readout index pair.1 ≠ readout index pair.2}
  have fullCover : pairUniverse ⊆ ⋃ index, separatedBy index := by
    intro pair distinct
    have someCoordinate :
        exists index, readout index pair.1 ≠ readout index pair.2 := by
      by_contra noCoordinate
      have sameFullReadout :
          jointReadout readout pair.1 = jointReadout readout pair.2 := by
        funext index
        by_contra different
        exact noCoordinate ⟨index, different⟩
      exact distinct (fullFaithful sameFullReadout)
    obtain ⟨index, separated⟩ := someCoordinate
    exact Set.mem_iUnion.mpr ⟨index, distinct, separated⟩
  have pairUniverseFinite : pairUniverse.Finite :=
    Set.finite_univ.subset (Set.subset_univ pairUniverse)
  rcases Set.finite_subset_iUnion pairUniverseFinite fullCover with
    ⟨selectedSet, selectedFinite, selectedCover⟩
  let selected : Finset Index := selectedFinite.toFinset
  refine ⟨selected, ?_⟩
  intro left right sameSelectedReadout
  by_contra distinct
  have pairCovered : (left, right) ∈ ⋃ index ∈ selectedSet, separatedBy index :=
    selectedCover (show (left, right) ∈ pairUniverse from distinct)
  rcases Set.mem_iUnion.mp pairCovered with ⟨index, pairCovered⟩
  rcases Set.mem_iUnion.mp pairCovered with ⟨indexSelected, separated⟩
  have indexInFinset : index ∈ selected := by
    simpa [selected] using indexSelected
  have equalAtIndex :=
    congrFun sameSelectedReadout ⟨index, indexInFinset⟩
  exact separated.2 equalAtIndex

#print axioms finite_faithful_subfamily_extraction

end D5.S3.ConceptDynamics.Faithfulness.FiniteFaithfulSubfamilyExtraction
