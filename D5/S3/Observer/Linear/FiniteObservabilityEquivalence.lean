/- GID: D5/S3/Observer/Linear/FiniteObservabilityEquivalence
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/FiniteObservabilityEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observability kernel, full rank, and Gram positivity are equivalent. -/

import D5.S3.Observer.Linear.DiscountedObservabilityGramianKernel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/- Library-search audit trail (2026-08-27):
   * D5 searches found discounted infinite-horizon Gramian results but no exact
     finite-horizon theorem equating residual triviality, full column rank, and
     strict Gram positivity.
   * Body-shape searches found no finite stacked-readout or finite Gramian D5
     definition, so both are constructed here from the source maps `T` and `C`.
   * Pinned Mathlib's `LinearMap.pi`, `LinearMap.finrank_range_add_finrank_ker`,
     `LinearMap.adjoint_inner_right`, and `List.TFAE` are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.FiniteObservabilityEquivalence

open InnerProductSpace Module
open scoped RealInnerProductSpace

/-- For a real finite-dimensional linear system, the zero finite-time readout
residual, full column rank of the stacked readout, and strict positivity of its
Gram operator are equivalent. -/
theorem finite_observability_equivalence
    {State Output : Type*}
    [NormedAddCommGroup State] [InnerProductSpace ℝ State]
    [FiniteDimensional ℝ State]
    [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
    [FiniteDimensional ℝ Output]
    (update : State →ₗ[ℝ] State) (readout : State →ₗ[ℝ] Output)
    (horizon : ℕ) :
    let observability :
        State →ₗ[ℝ] PiLp 2 (fun _ : Fin horizon => Output) :=
      (WithLp.linearEquiv 2 ℝ (Fin horizon -> Output)).symm.toLinearMap.comp
        (LinearMap.pi fun time : Fin horizon =>
          readout.comp (update ^ (time : ℕ)))
    let residual := LinearMap.ker observability
    let gram :=
      ((LinearMap.adjoint (𝕜 := ℝ) (E := State)
          (F := PiLp 2 (fun _ : Fin horizon => Output))) observability).comp
        observability
    List.TFAE [
      residual = ⊥,
      finrank ℝ (LinearMap.range observability) = finrank ℝ State,
      ∀ state : State, state ≠ 0 -> 0 < inner ℝ state (gram state)] := by
  let observability :
      State →ₗ[ℝ] PiLp 2 (fun _ : Fin horizon => Output) :=
    (WithLp.linearEquiv 2 ℝ (Fin horizon -> Output)).symm.toLinearMap.comp
      (LinearMap.pi fun time : Fin horizon =>
        readout.comp (update ^ (time : ℕ)))
  let residual := LinearMap.ker observability
  let gram :=
    ((LinearMap.adjoint (𝕜 := ℝ) (E := State)
        (F := PiLp 2 (fun _ : Fin horizon => Output))) observability).comp
      observability
  change List.TFAE [
    residual = ⊥,
    finrank ℝ (LinearMap.range observability) = finrank ℝ State,
    ∀ state : State, state ≠ 0 -> 0 < inner ℝ state (gram state)]
  tfae_have 1 ↔ 2 := by
    constructor
    · intro residualZero
      change LinearMap.ker observability = ⊥ at residualZero
      have rankNullity := observability.finrank_range_add_finrank_ker
      rw [residualZero, finrank_bot, add_zero] at rankNullity
      exact rankNullity
    · intro fullRank
      have rankNullity := observability.finrank_range_add_finrank_ker
      rw [fullRank] at rankNullity
      have kernelRankZero : finrank ℝ (LinearMap.ker observability) = 0 := by
        omega
      change LinearMap.ker observability = ⊥
      exact Submodule.finrank_eq_zero.1 kernelRankZero
  tfae_have 1 ↔ 3 := by
    constructor
    · intro residualZero state stateNonzero
      have observedNonzero : observability state ≠ 0 := by
        intro observedZero
        have stateInKernel : state ∈ residual := by
          simpa [residual, LinearMap.mem_ker] using observedZero
        rw [residualZero] at stateInKernel
        exact stateNonzero (by simpa using stateInKernel)
      change 0 < inner ℝ state (observability.adjoint (observability state))
      rw [observability.adjoint_inner_right]
      simpa [real_inner_self_eq_norm_sq] using
        (sq_pos_of_pos (norm_pos_iff.mpr observedNonzero))
    · intro gramPositive
      apply le_antisymm
      · intro state stateInResidual
        have observedZero : observability state = 0 := by
          simpa [residual, LinearMap.mem_ker] using stateInResidual
        by_contra stateNotBottom
        have stateNonzero : state ≠ 0 := by simpa using stateNotBottom
        have positive := gramPositive state stateNonzero
        change 0 < inner ℝ state
          (observability.adjoint (observability state)) at positive
        simp [observedZero] at positive
      · exact bot_le
  tfae_finish

#print axioms finite_observability_equivalence

end D5.S3.Observer.Linear.FiniteObservabilityEquivalence
