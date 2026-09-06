/- GID: D5/S3/Observer/Hankel/BalancedDeterminantInformationLoss
   generality: I
   mirror-B: D5/B/S3/Observer/Hankel/BalancedDeterminantInformationLoss
   mirror-E: none(waiver:parametric-exact-countermodel)
   anchors: []
   digest: Arbitrarily small certified balanced-truncation error does not preserve the original state determinant zeros. -/

import D5.S3.Observer.Hankel.BalancedTruncationTail
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Hankel.BalancedDeterminantInformationLoss

open Matrix
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open D5.S3.Observer.Hankel.BalancedTruncationStep
open D5.S3.Observer.Hankel.BalancedTruncationTail
open scoped BigOperators

/-- Two fixed strictly stable state modes. -/
def dynamics : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1 / 2, 1 / 4]

/-- Both the input and output port contain the weak mode, for every eps > 0. -/
def port (eps : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, eps]

/-- Exact common diagonal Stein weights, with the weak weight tending to zero. -/
def weights (eps : ℝ) : Fin 2 → ℝ := ![4 / 3, 16 * eps ^ 2 / 15]

/-- All states are instantaneously distinguishable by the output port.
The square input port is the same matrix, so this family has no hidden
zero-coupled channel for positive eps. -/
theorem port_injective (eps : ℝ) (heps : 0 < eps) : Function.Injective (port eps).mulVec := by
  intro x y h
  ext i
  fin_cases i
  · have h0 := congrFun h 0
    simpa [port, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · have h1 := congrFun h 1
    have he : eps * x 1 = eps * y 1 := by
      simpa [port, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
    exact mul_left_cancel₀ (ne_of_gt heps) he

/-- Every state is reachable by one input through the actual nonzero port. -/
theorem port_surjective (eps : ℝ) (heps : 0 < eps) : Function.Surjective (port eps).mulVec := by
  intro y
  refine ⟨![y 0, y 1 / eps], ?_⟩
  ext i
  fin_cases i <;> simp [port, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    div_eq_mul_inv, mul_comm, mul_left_comm, ne_of_gt heps]

/-- Both standard Stein inequalities hold by exact equality in this family. -/
theorem balanced_stein_data (eps : ℝ) (heps : 0 < eps) :
    BalancedStein (weights eps) dynamics (port eps) (port eps) := by
  have hO : ObservabilityStein (weights eps) dynamics (port eps) := by
    intro x
    apply le_of_eq
    norm_num [energy, squareSum, weights, dynamics, port, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    <;> ring
  refine ⟨?_, hO, ?_⟩
  · intro i
    fin_cases i <;> norm_num [weights] <;> positivity
  · intro x
    simpa [dynamics, port] using hO x

/-- The retained coordinate is genuinely the largest common Gramian weight. -/
theorem retained_weight_larger (eps : ℝ) (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    weights eps 1 ≤ weights eps 0 := by
  have hs := mul_self_le_mul_self h0 h1
  norm_num [weights]
  nlinarith [hs]

/-- The actual full determinant vanishes at z=4 and the actual retained
state determinant is -1 there, independently of the nonzero port size. -/
theorem actual_determinants_disagree :
    det (1 - (4 : ℝ) • dynamics) = 0 ∧
      det (1 - (4 : ℝ) • truncateA dynamics) = -1 := by
  norm_num [dynamics, truncateA, Matrix.det_fin_two, Matrix.det_fin_one,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply]

/-- The existing balanced-truncation theorem certifies arbitrarily weak
input-output effects for this actual reduction. -/
theorem actual_error_bound (eps : ℝ) (heps : 0 < eps)
    (u : ℕ → Fin 2 → ℝ) (N : ℕ) :
    windowNorm (fun k => matrixResponse dynamics (port eps) (port eps) u k -
      matrixResponse (truncateA dynamics) (truncateB (port eps))
        (truncateC (port eps)) u k) N ≤
      (32 * eps ^ 2 / 15) * windowNorm u N := by
  have h := single_truncation_window_bound (weights eps) dynamics (port eps) (port eps)
    (balanced_stein_data eps heps) u N
  convert h using 1 <;> norm_num [weights, Fin.last] <;> ring

/-- For every requested positive input-output error coefficient, an actually
ordered balanced family achieves a smaller certified coefficient while
losing the fixed state-determinant zero at z=4. This is a universal family,
not evidence from sampled eps values. -/
theorem arbitrarily_small_error_with_determinant_loss (eta : ℝ) (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      Function.Bijective (port eps).mulVec ∧
      BalancedStein (weights eps) dynamics (port eps) (port eps) ∧
      weights eps 1 ≤ weights eps 0 ∧ 32 * eps ^ 2 / 15 < eta ∧
      det (1 - (4 : ℝ) • dynamics) = 0 ∧
      det (1 - (4 : ℝ) • truncateA dynamics) ≠ 0 ∧
      ∀ (u : ℕ → Fin 2 → ℝ) (N : ℕ),
        windowNorm (fun k => matrixResponse dynamics (port eps) (port eps) u k -
          matrixResponse (truncateA dynamics) (truncateB (port eps))
            (truncateC (port eps)) u k) N ≤
          (32 * eps ^ 2 / 15) * windowNorm u N := by
  let eps : ℝ := min 1 (15 * eta / 64)
  have hpos : 0 < eps := lt_min (by norm_num) (by positivity)
  have h1 : eps ≤ 1 := min_le_left _ _
  have het : eps ≤ 15 * eta / 64 := min_le_right _ _
  have hsq : eps ^ 2 ≤ eps := by
    nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr h1)]
  have hsmall : 32 * eps ^ 2 / 15 < eta := by nlinarith
  refine ⟨eps, hpos, h1, ⟨port_injective eps hpos, port_surjective eps hpos⟩,
    balanced_stein_data eps hpos,
    retained_weight_larger eps hpos.le h1, hsmall, actual_determinants_disagree.1, ?_,
    actual_error_bound eps hpos⟩
  rw [actual_determinants_disagree.2]
  norm_num

#print axioms arbitrarily_small_error_with_determinant_loss

end D5.S3.Observer.Hankel.BalancedDeterminantInformationLoss
