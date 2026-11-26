/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/AlternatingMidpoint
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact midpoint trace gap for a pair of factors in a common affine span. -/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace RefinedBMV.Tracial

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def realDiagonal (a : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i ↦ (a i : ℂ)

private theorem trace_realDiagonal_pair (a c : ι → ℝ) (Y Z : Matrix ι ι ℂ) :
    (trace ((realDiagonal a * Y) * (realDiagonal c * Z))).re =
      ∑ i, ∑ j, a i * c j * (Y i j * Z j i).re := by
  simp only [realDiagonal, trace, diag_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.diagonal_mul]
  have h : ((a i : ℂ) * Y i j) * ((c j : ℂ) * Z j i) =
      ((a i * c j : ℝ) : ℂ) * (Y i j * Z j i) := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]

/-- With a common Hermitian direction for both affine factors, the loss
from averaging the diagonal factors is a sum of weighted squares.
The diagonal factors may have zero entries. -/
theorem alternating_affine_midpoint_gap (a c : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (J : Matrix ι ι ℂ) (hJ : J.IsHermitian) (u v r t : ℝ) :
    let Y : Matrix ι ι ℂ := (u : ℂ) • (1 : Matrix ι ι ℂ) + (r : ℂ) • J
    let Z : Matrix ι ι ℂ := (v : ℂ) • (1 : Matrix ι ι ℂ) + (t : ℂ) • J
    let d := realDiagonal (fun i ↦ Real.sqrt (a i * c i))
    (trace ((realDiagonal a * Y) * (realDiagonal c * Z))).re -
      (trace ((d * Y) * (d * Z))).re =
      (r * t / 2) * ∑ i, ∑ j,
        (Real.sqrt (a i * c j) - Real.sqrt (a j * c i)) ^ 2 * ‖J i j‖ ^ 2 := by
  classical
  dsimp only
  let Y : Matrix ι ι ℂ := (u : ℂ) • (1 : Matrix ι ι ℂ) + (r : ℂ) • J
  let Z : Matrix ι ι ℂ := (v : ℂ) • (1 : Matrix ι ι ℂ) + (t : ℂ) • J
  let w : ι → ι → ℝ := fun i j ↦ (Y i j * Z j i).re
  have hj (i j : ι) : J j i = (starRingEnd ℂ) (J i j) := by
    have h := congrFun (congrFun hJ.eq j) i
    simpa only [Matrix.conjTranspose_apply, Complex.star_def] using h.symm
  have hoff (i j : ι) (h : i ≠ j) : w i j = r * t * ‖J i j‖ ^ 2 := by
    simp only [w, Y, Z, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      ite_eq_right h, ite_eq_right (Ne.symm h), smul_eq_mul, mul_zero, zero_add, hj i j]
    have he : ((r : ℂ) * J i j) * ((t : ℂ) * (starRingEnd ℂ) (J i j)) =
        ((r * t : ℝ) : ℂ) * (J i j * (starRingEnd ℂ) (J i j)) := by
      push_cast
      ring
    rw [he, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hw (i j : ι) : w i j = w j i := by
    by_cases he : i = j
    · subst j
      rfl
    rw [hoff i j he, hoff j i (Ne.symm he), hj i j, Complex.norm_conj]
  have hs : (∑ i, ∑ j, a i * c j * w i j) = ∑ i, ∑ j, a j * c i * w i j := by
    rw [Finset.sum_comm]
    simp_rw [hw]
  have hswap (i j : ι) :
      Real.sqrt (a i * c i) * Real.sqrt (a j * c j) =
        Real.sqrt (a i * c j) * Real.sqrt (a j * c i) := by
    rw [← Real.sqrt_mul (mul_nonneg (ha i) (hc i)),
      ← Real.sqrt_mul (mul_nonneg (ha i) (hc j))]
    congr 1
    ring
  have hpair (i j : ι) :
      (a i * c j + a j * c i) * w i j / 2 -
        Real.sqrt (a i * c i) * Real.sqrt (a j * c j) * w i j =
      r * t / 2 *
        ((Real.sqrt (a i * c j) - Real.sqrt (a j * c i)) ^ 2 * ‖J i j‖ ^ 2) := by
    by_cases he : i = j
    · subst j
      have hsq := Real.sq_sqrt (mul_nonneg (ha i) (hc i))
      rw [sub_self, zero_pow (by norm_num)]
      nlinarith only [congrArg (fun x ↦ x * w i i) hsq]
    rw [hswap, hoff i j he]
    have hp := Real.sq_sqrt (mul_nonneg (ha i) (hc j))
    have hq := Real.sq_sqrt (mul_nonneg (ha j) (hc i))
    calc
      _ = r * t / 2 *
          ((a i * c j + a j * c i - 2 * Real.sqrt (a i * c j) *
            Real.sqrt (a j * c i)) * ‖J i j‖ ^ 2) := by ring
      _ = _ := by
        have hsq : (Real.sqrt (a i * c j) - Real.sqrt (a j * c i)) ^ 2 =
            a i * c j + a j * c i -
              2 * Real.sqrt (a i * c j) * Real.sqrt (a j * c i) := by
          nlinarith only [hp, hq]
        rw [hsq]
  change (trace ((realDiagonal a * Y) * (realDiagonal c * Z))).re -
      (trace ((realDiagonal _ * Y) * (realDiagonal _ * Z))).re = _
  rw [trace_realDiagonal_pair, trace_realDiagonal_pair]
  change (∑ i, ∑ j, a i * c j * w i j) -
      (∑ i, ∑ j, Real.sqrt (a i * c i) * Real.sqrt (a j * c j) * w i j) = _
  calc
    _ = ∑ i, ∑ j, ((a i * c j + a j * c i) * w i j / 2 -
          Real.sqrt (a i * c i) * Real.sqrt (a j * c j) * w i j) := by
      simp only [add_mul, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
      rw [← hs]
      ring
    _ = _ := by
      simp_rw [hpair, ← Finset.mul_sum]

end RefinedBMV.Tracial
