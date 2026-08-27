/- GID: D5/S3/Observer/Linear/ObservationRankMonotonicity
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/ObservationRankMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observation-subspace rank is monotone under inclusion. -/

import D5.S3.Observer.Linear.ObservationRankSubmodularity

/- Library-search audit trail (2026-08-27):
   * The current D5 tree has no exact theorem for monotonicity of the rank of
     selected observation subspaces. `ObservationRankSubmodularity` is adjacent
     but states submodularity and diminishing returns for finite selections.
   * The body-shape search for an indexed supremum of selected subspaces found
     no canonical D5 definition to import.
   * Pinned Mathlib's `iSup_le`, `le_iSup_of_le`, and
     `Submodule.finrank_mono` are the exact component results used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.ObservationRankMonotonicity

/-- Enlarging an arbitrary set of observation indices can only enlarge the
sum of their subspaces, hence cannot decrease its finite-dimensional rank. -/
theorem observation_rank_monotonicity
    {K V Index : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (observationSubspace : Index -> Submodule K V) :
    forall selected larger : Set Index, selected ⊆ larger ->
      Module.finrank K
          ((⨆ index : ↥selected, observationSubspace index.1) :
            Submodule K V) <=
        Module.finrank K
          ((⨆ index : ↥larger, observationSubspace index.1) :
            Submodule K V) := by
  intro selected larger inclusion
  apply Submodule.finrank_mono
  refine iSup_le fun index => ?_
  exact le_iSup_of_le
    (⟨index.1, inclusion index.2⟩ : larger) le_rfl

#print axioms observation_rank_monotonicity

end D5.S3.Observer.Linear.ObservationRankMonotonicity
