/- GID: D5/S3/Dynamics/Koopman/FiniteKoopmanUnitary
   generality: G
   mirror-B: D5/B/S3/Dynamics/Koopman/FiniteKoopmanUnitary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pullback by a finite permutation preserves observable norm, has inverse pullback, and periodic eigenvalues are roots of unity. -/

import D5.S3.Dynamics.Koopman.DiscreteKoopmanOperator
import Mathlib.Tactic

/-!
# Finite permutation Koopman unitarity

On a finite state space, a permutation update reindexes observables.  Its
Koopman pullback preserves the unnormalized finite `l2` norm and is inverted by
pullback along the inverse permutation.  If the state permutation has finite
period `m`, every nonzero Koopman eigenfunction has eigenvalue satisfying
`lambda^m = 1`.

This is the finite algebraic content of unitarity.  It does not construct a
completed Hilbert space, spectral measure, continuous-time generator, or
resonance expansion.
-/

/- Library-search audit trail (2026-09-01):
   * `DiscreteKoopmanOperator` owns the linear pullback, finite iterates, and
     eigenfunction laws.
   * Existing observable-closure modules own generated algebras, not norm
     preservation or finite-cycle eigenvalue constraints.
   * Repository search found no finite permutation Koopman unitarity theorem.
   * Pinned Mathlib supplies finite equivalence reindexing and function
     iteration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Dynamics.Koopman.FiniteKoopmanUnitary

open D5.S3.Dynamics.Koopman.DiscreteKoopmanOperator

noncomputable section

universe u

variable {State : Type u} [Fintype State]

/-- Unnormalized finite squared `l2` norm of a complex observable. -/
def finiteObservableNormSq (observable : State → ℂ) : ℝ :=
  ∑ state, ‖observable state‖ ^ 2

/-- Koopman pullback by a finite permutation preserves the squared norm. -/
theorem finiteObservableNormSq_koopman
    (update : Equiv.Perm State) (observable : State → ℂ) :
    finiteObservableNormSq
        (discreteKoopmanOperator (update : State → State) observable) =
      finiteObservableNormSq observable := by
  unfold finiteObservableNormSq discreteKoopmanOperator
  simpa using update.sum_comp (fun state => ‖observable state‖ ^ 2)

/-- Pullback along the inverse permutation is a left inverse. -/
theorem koopman_inverse_left
    (update : Equiv.Perm State) (observable : State → ℂ) :
    discreteKoopmanOperator (update.symm : State → State)
        (discreteKoopmanOperator (update : State → State) observable) =
      observable := by
  funext state
  simp [discreteKoopmanOperator]

/-- Pullback along the inverse permutation is a right inverse. -/
theorem koopman_inverse_right
    (update : Equiv.Perm State) (observable : State → ℂ) :
    discreteKoopmanOperator (update : State → State)
        (discreteKoopmanOperator (update.symm : State → State) observable) =
      observable := by
  funext state
  simp [discreteKoopmanOperator]

/-- The finite Koopman pullback is injective for a permutation update. -/
theorem permutationKoopman_injective
    (update : Equiv.Perm State) :
    Function.Injective
      (discreteKoopmanOperator (update : State → State)) := by
  intro first second hEqual
  have hInverse := congrArg
    (fun observable =>
      discreteKoopmanOperator (update.symm : State → State) observable)
    hEqual
  simpa [koopman_inverse_left] using hInverse

/-- A nonzero finite-period Koopman eigenfunction has a root-of-unity
eigenvalue. -/
theorem koopman_eigenvalue_pow_period_eq_one
    (update : Equiv.Perm State) (period : ℕ)
    (hPeriod : ((update : State → State)^[period]) = id)
    {observable : State → ℂ} {eigenvalue : ℂ}
    (hEigen : IsKoopmanEigenfunction
      (update : State → State) observable eigenvalue)
    (hObservable : observable ≠ 0) :
    eigenvalue ^ period = 1 := by
  have hPoint : ∃ state, observable state ≠ 0 := by
    by_contra hNoPoint
    push_neg at hNoPoint
    apply hObservable
    funext state
    exact hNoPoint state
  obtain ⟨state, hState⟩ := hPoint
  have hIterate := koopmanIterate_eigenfunction
    (update : State → State) hEigen period
  have hAtState := congrFun hIterate state
  have hUpdate : ((update : State → State)^[period]) state = state := by
    exact congrFun hPeriod state
  change
    observable (((update : State → State)^[period]) state) =
      eigenvalue ^ period * observable state at hAtState
  rw [hUpdate] at hAtState
  apply mul_right_cancel₀ hState
  simpa using hAtState.symm

/-- If one period is positive, the eigenvalue of a nonzero eigenfunction is
nonzero. -/
theorem koopman_eigenvalue_ne_zero_of_positive_period
    (update : Equiv.Perm State) (period : ℕ) (hPositive : 0 < period)
    (hPeriod : ((update : State → State)^[period]) = id)
    {observable : State → ℂ} {eigenvalue : ℂ}
    (hEigen : IsKoopmanEigenfunction
      (update : State → State) observable eigenvalue)
    (hObservable : observable ≠ 0) :
    eigenvalue ≠ 0 := by
  intro hZero
  have hPower := koopman_eigenvalue_pow_period_eq_one
    update period hPeriod hEigen hObservable
  rw [hZero, zero_pow hPositive] at hPower
  norm_num at hPower

/-- The identity permutation gives the identity Koopman pullback. -/
theorem identity_permutation_koopman
    (observable : State → ℂ) :
    discreteKoopmanOperator ((1 : Equiv.Perm State) : State → State)
      observable = observable := by
  rfl

example :
    finiteObservableNormSq
      (discreteKoopmanOperator
        ((1 : Equiv.Perm (Fin 1)) : Fin 1 → Fin 1) (fun _ => 1)) = 1 := by
  simp [finiteObservableNormSq, discreteKoopmanOperator]

#print axioms finiteObservableNormSq_koopman
#print axioms koopman_inverse_left
#print axioms koopman_inverse_right
#print axioms permutationKoopman_injective
#print axioms koopman_eigenvalue_pow_period_eq_one
#print axioms koopman_eigenvalue_ne_zero_of_positive_period
#print axioms identity_permutation_koopman

end

end D5.S3.Dynamics.Koopman.FiniteKoopmanUnitary
