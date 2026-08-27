/- GID: D5/S3/Observer/Linear/DualGramVisibleRanges
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/DualGramVisibleRanges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dual Gram operators expose exactly the state and protocol visible ranges. -/

/- Library-search audit trail (2026-08-28):
   * The D5 body-shape search found `LinearMap.pi` already used as the canonical
     indexed-readout constructor in `FiniteObservabilityEquivalence`; the public
     observation map below reuses that primitive and introduces no new definition.
   * D5 searches for adjoint-composition range equalities found no existing
     theorem packaging both state-side and protocol-side clauses.
   * Pinned Mathlib provides the exact component lemmas
     `LinearMap.range_adjoint_comp_self` and
     `LinearMap.range_self_comp_adjoint`; both are applied directly. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Pi

namespace D5.S3.Observer.Linear.DualGramVisibleRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For an indexed family of linear protocol readouts, construct the observation
map coordinatewise. The ranges of its two Gram operators are exactly the
state-side span produced by the adjoint and the realizable protocol-side range. -/
theorem dual_gram_visible_ranges
    {K V ι : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V] [Fintype ι]
    (readout : ι -> V →ₗ[K] K) :
    let observation : V →ₗ[K] PiLp 2 (fun _ : ι => K) :=
      (WithLp.linearEquiv 2 K (ι -> K)).symm.toLinearMap.comp
        (LinearMap.pi readout)
    (observation.adjoint ∘ₗ observation).range = observation.adjoint.range ∧
      (observation ∘ₗ observation.adjoint).range = observation.range := by
  dsimp only
  exact ⟨LinearMap.range_adjoint_comp_self _,
    LinearMap.range_self_comp_adjoint _⟩

#print axioms dual_gram_visible_ranges

end D5.S3.Observer.Linear.DualGramVisibleRanges
