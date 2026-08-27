/- GID: D5/S3/Observer/Refinement/DependentFinitePrimeTimeTomography
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/DependentFinitePrimeTimeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dependent finite prime-time separation has a finite window. -/

import D5.S3.ConceptDynamics.Faithfulness.FiniteFaithfulSubfamilyExtraction

/- Library-search audit trail (2026-08-27):
   * Repository name and body-shape searches found the canonical dependent
     product `jointReadout`, which is used directly for both complete and
     finite-window observations.
   * Exact D5 hit `finite_faithful_subfamily_extraction` supplies a finite set
     of separating index-time coordinates and is applied below.
   * `BiaxialMonotoneRefinement` constructs the same orbit-readout body only
     for natural-number indices and a common output carrier, so it is not the
     source's arbitrary dependent observer family.
   * Pinned Mathlib searches found no whole finite prime-time tomography
     theorem. `Finset.le_sup` supplies the supporting finite time bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.DependentFinitePrimeTimeTomography

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Faithfulness.FiniteFaithfulSubfamilyExtraction

universe u v w

/-- If the complete dependent family of index-time observations separates a
finite state carrier, then finitely many observer indices and one finite time
horizon already separate it. The finite window retains each index's original
dependent output carrier. -/
theorem dependent_finite_prime_time_tomography
    {X : Type u} {Index : Type v} {Output : Index -> Type w} [Finite X]
    (update : X -> X) (readout : forall index, X -> Output index)
    (completeSeparation :
      Function.Injective
        (jointReadout
          (fun coordinate : Index × Nat => fun state =>
            readout coordinate.1 ((update^[coordinate.2]) state)))) :
    exists (selected : Finset Index) (depth : Nat),
      Function.Injective
        (jointReadout
          (fun coordinate : {candidate : Index × Nat //
              candidate.1 ∈ selected ∧ candidate.2 <= depth} =>
            fun state =>
              readout coordinate.1.1
                ((update^[coordinate.1.2]) state))) := by
  classical
  let timedReadout : forall coordinate : Index × Nat, X -> Output coordinate.1 :=
    fun coordinate state =>
      readout coordinate.1 ((update^[coordinate.2]) state)
  have timedSeparation : Function.Injective (jointReadout timedReadout) := by
    simpa only [timedReadout] using completeSeparation
  obtain ⟨coordinates, coordinatesSeparate⟩ :=
    finite_faithful_subfamily_extraction timedReadout timedSeparation
  let selected : Finset Index := coordinates.image Prod.fst
  let depth : Nat := coordinates.sup Prod.snd
  refine ⟨selected, depth, ?_⟩
  intro left right sameWindow
  apply coordinatesSeparate
  funext coordinate
  have indexSelected : coordinate.1.1 ∈ selected := by
    simp only [selected, Finset.mem_image]
    exact ⟨coordinate.1, coordinate.2, rfl⟩
  have timeBound : coordinate.1.2 <= depth := by
    exact Finset.le_sup coordinate.2
  let windowCoordinate : {candidate : Index × Nat //
      candidate.1 ∈ selected ∧ candidate.2 <= depth} :=
    ⟨coordinate.1, indexSelected, timeBound⟩
  change readout coordinate.1.1 ((update^[coordinate.1.2]) left) =
    readout coordinate.1.1 ((update^[coordinate.1.2]) right)
  have equalAtCoordinate := congrFun sameWindow windowCoordinate
  change readout windowCoordinate.1.1
      ((update^[windowCoordinate.1.2]) left) =
    readout windowCoordinate.1.1
      ((update^[windowCoordinate.1.2]) right) at equalAtCoordinate
  simpa only [windowCoordinate] using equalAtCoordinate

#print axioms dependent_finite_prime_time_tomography

end D5.S3.Observer.Refinement.DependentFinitePrimeTimeTomography
