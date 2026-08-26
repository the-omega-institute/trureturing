/- GID: D5/S3/Observer/Refinement/BiaxialObservationRefinement
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/BiaxialObservationRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint index and time refinement enlarges schedules and shrinks indistinguishability. -/

import D5.S3.Observer.Refinement.BiaxialMonotoneRefinement

/- Library-search audit trail (2026-08-26):
   * Exact repository hit `biaxial_monotone` proves the source's
     indistinguishability inclusion and is applied directly below.
   * Its public signature does not expose the preceding observation-schedule
     inclusion, so it is a close hit rather than an exact whole-statement bind.
   * `observationSchedule` and `Indist` are the canonical family primitives;
     name and body-shape searches found no theorem already conjoining both
     inclusions. Pinned Mathlib supplies `Nat.lt_of_lt_of_le` for the time axis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.BiaxialObservationRefinement

open D5.S3.Observer.Refinement.BiaxialMonotoneRefinement

/-- Enlarging the observation-index set and time horizon includes the smaller
schedule in the larger one and reverses inclusion of their indistinguishability
relations. -/
theorem biaxial_observation_refinement
    {X O : Type*} (J K : Finset Nat) (m n : Nat)
    (readout : Nat -> X -> O) (T : X -> X)
    (hJK : J ⊆ K) (hmn : m ≤ n) :
    observationSchedule J m ⊆ observationSchedule K n ∧
      Indist K n readout T ⊆ Indist J m readout T := by
  constructor
  · intro index hindex
    exact ⟨hJK hindex.1, Nat.lt_of_lt_of_le hindex.2 hmn⟩
  · exact biaxial_monotone J K m n readout T hJK hmn

#print axioms biaxial_observation_refinement

end D5.S3.Observer.Refinement.BiaxialObservationRefinement
