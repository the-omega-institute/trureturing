/- GID: D5/S3/Observer/LinearMemory/ObservationRankEquality
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/ObservationRankEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The ranks of a readout map and its two Gram compositions coincide. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.ObservationRankEquality

open scoped RealInnerProductSpace

theorem observation_rank_equality
    {K X P : Type*} [RCLike K]
    [NormedAddCommGroup X] [InnerProductSpace K X]
    [NormedAddCommGroup P] [InnerProductSpace K P]
    [FiniteDimensional K X] [FiniteDimensional K P]
    (readout : X →ₗ[K] P) :
    Module.finrank K ((readout.adjoint ∘ₗ readout).range) =
        Module.finrank K readout.range ∧
      Module.finrank K readout.range =
        Module.finrank K ((readout ∘ₗ readout.adjoint).range) := by
  constructor
  · rw [LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint]
  · rw [LinearMap.range_self_comp_adjoint]

#print axioms observation_rank_equality

end D5.S3.Observer.LinearMemory.ObservationRankEquality
