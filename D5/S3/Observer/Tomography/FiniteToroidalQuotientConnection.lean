/- GID: D5/S3/Observer/Tomography/FiniteToroidalQuotientConnection
   generality: I
   mirror-B: D5/B/S3/Observer/Tomography/FiniteToroidalQuotientConnection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite positive toroidal Gram kernels recover their common complex factor. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.BigOperators

/- Library-search audit trail (2026-09-01):
   * The target atom has no formalization receipt. Exact D5 searches for a toroidal
     Gram-kernel quotient and its two-point factorization found no whole-statement owner.
   * `finite_toroidal_frame_reconstruction` is the adjacent exact single-point
     inner-product reconstruction. It neither defines the two-point Gram kernel nor states
     the quotient identity below. `weighted_kernel_completeness` concerns a real quadratic
     Gramian and has no complex common-factor quotient.
   * Pinned Mathlib supplies `Finset.mul_sum`, multiplicativity of complex conjugation,
     `Complex.mul_conj`, `Finset.sum_pos'`, and `mul_div_cancel_right₀`; they are applied
     directly. It has no toroidal-period or completed-zeta specialization of this result.
   * Searches of the other pinned Lean packages found no toroidal-period or weighted-Gram
     quotient theorem. Lean LSP was not exposed in this worker, so repository and pinned
     source/declaration searches were used directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Tomography.FiniteToroidalQuotientConnection

open scoped BigOperators

/-- The source's finite weighted sesquilinear Gram kernel. -/
def weightedGramKernel {Index : Type*} (selected : Finset Index)
    (weights : Index -> Real) (readout : Index -> ℂ -> ℂ) (s t : ℂ) : ℂ :=
  ∑ index ∈ selected,
    (weights index : ℂ) * readout index s * starRingEnd ℂ (readout index t)

/-- The local quotient of the period Gram kernel by the carrier Gram kernel. -/
def localQuotientKernel {Index : Type*} (selected : Finset Index)
    (weights : Index -> Real) (period twist : Index -> ℂ -> ℂ) (s t : ℂ) : ℂ :=
  weightedGramKernel selected weights period s t /
    weightedGramKernel selected weights twist s t

/-- A common pointwise factor pulls out of both slots of the finite Gram kernel. -/
theorem weighted_gram_kernel_factorization {Index : Type*}
    (selected : Finset Index) (weights : Index -> Real)
    (period twist : Index -> ℂ -> ℂ) (xi : ℂ -> ℂ)
    (factorization : ∀ index ∈ selected, ∀ point,
      period index point = xi point * twist index point) (s t : ℂ) :
    weightedGramKernel selected weights period s t =
      xi s * starRingEnd ℂ (xi t) * weightedGramKernel selected weights twist s t := by
  classical
  unfold weightedGramKernel
  calc
    _ = ∑ index ∈ selected,
        (xi s * starRingEnd ℂ (xi t)) *
          ((weights index : ℂ) * twist index s *
            starRingEnd ℂ (twist index t)) := by
      apply Finset.sum_congr rfl
      intro index indexSelected
      rw [factorization index indexSelected s, factorization index indexSelected t]
      simp only [map_mul]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- Positive weights and one nonzero carrier coordinate make the diagonal Gram value nonzero. -/
theorem weighted_gram_kernel_diagonal_ne_zero {Index : Type*}
    (selected : Finset Index) (weights : Index -> Real)
    (twist : Index -> ℂ -> ℂ) (weightsPositive : ∀ index ∈ selected, 0 < weights index)
    (point : ℂ) (pointwiseNonvanishing : ∃ index, index ∈ selected ∧ twist index point ≠ 0) :
    weightedGramKernel selected weights twist point point ≠ 0 := by
  classical
  have positiveRealSum :
      0 < ∑ index ∈ selected, weights index * Complex.normSq (twist index point) := by
    apply Finset.sum_pos'
    · intro index indexSelected
      exact mul_nonneg (le_of_lt (weightsPositive index indexSelected))
        (Complex.normSq_nonneg _)
    · obtain ⟨index, indexSelected, twistNonzero⟩ := pointwiseNonvanishing
      exact ⟨index, indexSelected,
        mul_pos (weightsPositive index indexSelected) (Complex.normSq_pos.mpr twistNonzero)⟩
  have kernelAsReal :
      weightedGramKernel selected weights twist point point =
        ((∑ index ∈ selected, weights index * Complex.normSq (twist index point) : Real) : ℂ) := by
    unfold weightedGramKernel
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro index indexSelected
    simp [mul_assoc, Complex.mul_conj]
  rw [kernelAsReal]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt positiveRealSum)

/--
For a finite positive toroidal family, pointwise carrier nonvanishing makes the
carrier Gram kernel nonzero on the diagonal. Wherever that kernel remains
nonzero, the local Gram quotient is the common factor in the first slot times
the conjugate common factor in the second slot.
-/
theorem finite_toroidal_frame_quotient_connection {Index : Type*}
    (window : Set ℂ) (selected : Finset Index) (weights : Index -> Real)
    (period twist : Index -> ℂ -> ℂ) (xi : ℂ -> ℂ)
    (weightsPositive : ∀ index ∈ selected, 0 < weights index)
    (factorization : ∀ index ∈ selected, ∀ point,
      period index point = xi point * twist index point)
    (pointwiseNonvanishing : ∀ point ∈ window,
      ∃ index, index ∈ selected ∧ twist index point ≠ 0) :
    (∀ point ∈ window, weightedGramKernel selected weights twist point point ≠ 0) ∧
      ∀ s t, weightedGramKernel selected weights twist s t ≠ 0 ->
        localQuotientKernel selected weights period twist s t =
          xi s * starRingEnd ℂ (xi t) := by
  constructor
  · intro point pointInWindow
    exact weighted_gram_kernel_diagonal_ne_zero selected weights twist weightsPositive point
      (pointwiseNonvanishing point pointInWindow)
  · intro s t carrierKernelNonzero
    unfold localQuotientKernel
    rw [weighted_gram_kernel_factorization selected weights period twist xi factorization s t]
    exact mul_div_cancel_right₀ _ carrierKernelNonzero

example :
    let selected : Finset Unit := {()}
    let weights : Unit -> Real := fun _ => 1
    let period : Unit -> ℂ -> ℂ := fun _ _ => 2
    let twist : Unit -> ℂ -> ℂ := fun _ _ => 1
    let xi : ℂ -> ℂ := fun _ => 2
    (∀ point ∈ ({0} : Set ℂ),
        weightedGramKernel selected weights twist point point ≠ 0) ∧
      ∀ s t, weightedGramKernel selected weights twist s t ≠ 0 ->
        localQuotientKernel selected weights period twist s t =
          xi s * starRingEnd ℂ (xi t) := by
  apply finite_toroidal_frame_quotient_connection
  · simp
  · intro index indexSelected point
    simp
  · intro point pointInWindow
    exact ⟨(), by simp, by norm_num⟩

example :
    let selected : Finset Unit := {()}
    let weights : Unit -> Real := fun _ => 1
    let period : Unit -> ℂ -> ℂ := fun _ _ => 0
    let twist : Unit -> ℂ -> ℂ := fun _ _ => 0
    let xi : ℂ -> ℂ := fun _ => 1
    (∀ index ∈ selected, 0 < weights index) ∧
      (∀ index ∈ selected, ∀ point, period index point = xi point * twist index point) ∧
      weightedGramKernel selected weights twist 0 0 = 0 ∧
      localQuotientKernel selected weights period twist 0 0 ≠
        xi 0 * starRingEnd ℂ (xi 0) := by
  norm_num [weightedGramKernel, localQuotientKernel]

#print axioms weightedGramKernel
#print axioms localQuotientKernel
#print axioms weighted_gram_kernel_factorization
#print axioms weighted_gram_kernel_diagonal_ne_zero
#print axioms finite_toroidal_frame_quotient_connection

end D5.S3.Observer.Tomography.FiniteToroidalQuotientConnection
