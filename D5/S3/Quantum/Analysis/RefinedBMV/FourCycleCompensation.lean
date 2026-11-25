/- GID: D5/S3/Quantum/Analysis/RefinedBMV/FourCycleCompensation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compensation of a signed four-cycle by its four spectral backtracks. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Four-cycle compensation for quartic spectral trace sums -/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace RefinedBMV

private theorem cycle_abs_trace_le {i j : Type*} [Fintype i] [Fintype j]
    (X : Matrix i j ℂ) (Y : Matrix j i ℂ) :
    |(trace (X * Y)).re| ≤ ‖X‖ * ‖Y‖ := by
  let flatten (A : Matrix j i ℂ) : EuclideanSpace ℂ (j × i) :=
    WithLp.toLp 2 fun uv ↦ A uv.1 uv.2
  have hnorm (A : Matrix j i ℂ) : ‖flatten A‖ = ‖A‖ := by
    rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
      Fintype.sum_prod_type]
    simp [flatten, Real.rpow_two]
  have hinner : inner ℂ (flatten Xᴴ) (flatten Y) = trace (X * Y) := by
    simp only [PiLp.inner_apply, flatten, RCLike.inner_apply', Fintype.sum_prod_type,
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.conj_conj]
    exact Finset.sum_comm
  have h := norm_inner_le_norm (𝕜 := ℂ) (flatten Xᴴ) (flatten Y)
  rw [hinner, hnorm, hnorm, Matrix.frobenius_norm_conjTranspose] at h
  exact (Complex.abs_re_le_norm _).trans h

private theorem cycle_pair_compensation {a b x y t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : t ≤ x * y) :
    2 * Real.sqrt (a * b) * t ≤ a * x ^ 2 + b * y ^ 2 := by
  rw [Real.sqrt_mul ha]
  calc
    _ ≤ 2 * (Real.sqrt a * Real.sqrt b) * (x * y) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 2 * (Real.sqrt a * x) * (Real.sqrt b * y) := by ring
    _ ≤ (Real.sqrt a * x) ^ 2 + (Real.sqrt b * y) ^ 2 := by
      nlinarith only [sq_nonneg (Real.sqrt a * x - Real.sqrt b * y)]
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Two pairings of the four backtracks can pay for a signed four-cycle.
The index types can differ, as they do for distinct spectral multiplicities. -/
theorem four_cycle_compensation {i j k l : Type*}
    [Fintype i] [Fintype j] [Fintype k] [Fintype l]
    (X : Matrix i j ℂ) (Y : Matrix j k ℂ) (Z : Matrix k l ℂ) (W : Matrix l i ℂ)
    {a b c d w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hw : 0 ≤ w)
    (hweight : w ≤ Real.sqrt (a * c) + Real.sqrt (b * d)) :
    0 ≤ a * ‖W * X‖ ^ 2 + b * ‖X * Y‖ ^ 2 + c * ‖Y * Z‖ ^ 2 + d * ‖Z * W‖ ^ 2
      + 2 * w * (trace (X * Y * Z * W)).re := by
  let t := (trace (X * Y * Z * W)).re
  have hac : |t| ≤ ‖W * X‖ * ‖Y * Z‖ := by
    have htrace : trace ((W * X) * (Y * Z)) = trace (X * Y * Z * W) := by
      simpa only [Matrix.mul_assoc] using (trace_mul_comm W (X * Y * Z))
    simpa only [htrace, t] using cycle_abs_trace_le (W * X) (Y * Z)
  have hbd : |t| ≤ ‖X * Y‖ * ‖Z * W‖ := by
    simpa only [Matrix.mul_assoc, t] using cycle_abs_trace_le (X * Y) (Z * W)
  have h1 := cycle_pair_compensation ha hc hac
  have h2 := cycle_pair_compensation hb hd hbd
  have h3 := mul_le_mul_of_nonneg_right hweight
    (show 0 ≤ 2 * |t| by positivity)
  have h4 := mul_le_mul_of_nonneg_left (neg_abs_le t)
    (show 0 ≤ 2 * w by positivity)
  change 0 ≤ _ + 2 * w * t
  linarith only [h1, h2, h3, h4]

private theorem frobenius_sq_entries {i j : Type*} [Fintype i] [Fintype j]
    (A : Matrix i j ℂ) : ‖A‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  change ‖WithLp.toLp 2 (fun a => WithLp.toLp 2 (A a))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2]

private theorem frobenius_sq_trace {i j : Type*} [Fintype i] [Fintype j]
    (A : Matrix i j ℂ) : ((‖A‖ ^ 2 : ℝ) : ℂ) = trace (Aᴴ * A) := by
  rw [frobenius_sq_entries, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_pow, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']
  rw [Finset.sum_comm]

private theorem gram_product_bound {t i j : Type*} [Fintype t] [Fintype i] [Fintype j]
    (A : Matrix t i ℂ) (B : Matrix t j ℂ) :
    ‖Aᴴ * B‖ ≤ Real.sqrt (‖A * Aᴴ‖ * ‖B * Bᴴ‖) := by
  have htrace : trace ((Aᴴ * B)ᴴ * (Aᴴ * B)) =
      trace ((A * Aᴴ) * (B * Bᴴ)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Bᴴ (A * Aᴴ * B)
  have h := cycle_abs_trace_le (A * Aᴴ) (B * Bᴴ)
  rw [← htrace, ← frobenius_sq_trace, Complex.ofReal_re, abs_of_nonneg (sq_nonneg _)] at h
  exact Real.le_sqrt_of_sq_le h

private theorem frobenius_diagonal_bound {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i]
    (d : i → ℂ) (X : Matrix i j ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hd : ∀ a, ‖d a‖ ≤ M) :
    ‖diagonal d * X‖ ≤ M * ‖X‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  rw [mul_pow, frobenius_sq_entries (diagonal d * X), frobenius_sq_entries X, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ ↦ ?_
  rw [Matrix.diagonal_mul, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hM).mpr (hd a)) (sq_nonneg _)

/-- Grouping the two lower spectral slots bounds their entire trace by the
Frobenius norm of the compressed product and the two outer Gram norms. -/
theorem exceptional_residue_trace_le {t i j : Type*}
    [Fintype t] [Fintype i] [Fintype j] [DecidableEq j]
    (C : Matrix t i ℂ) (E : Matrix i j ℂ) (F : Matrix j j ℂ) (Z : Matrix t j ℂ)
    (d : j → ℂ) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ a, ‖d a‖ ≤ M) :
    let S := diagonal d
    let R := S * S
    |(trace (C * E * R * F * R * Zᴴ)).re| ≤
      ‖E * R * F * S‖ * (M * Real.sqrt (‖Z * Zᴴ‖ * ‖C * Cᴴ‖)) := by
  dsimp only
  let S := diagonal d
  let R := S * S
  let Y := E * R * F * S
  have htrace : trace (Y * (S * (Zᴴ * C))) = trace (C * E * R * F * R * Zᴴ) := by
    calc
      _ = trace ((Y * S * Zᴴ) * C) := by simp only [Matrix.mul_assoc]
      _ = trace (C * (Y * S * Zᴴ)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Y, R, Matrix.mul_assoc]
  calc
    _ ≤ ‖Y‖ * ‖S * (Zᴴ * C)‖ := by
      simpa only [htrace] using cycle_abs_trace_le Y (S * (Zᴴ * C))
    _ ≤ ‖Y‖ * (M * Real.sqrt (‖Z * Zᴴ‖ * ‖C * Cᴴ‖)) :=
      mul_le_mul_of_nonneg_left
        ((frobenius_diagonal_bound d (Zᴴ * C) hM hd).trans
          (mul_le_mul_of_nonneg_left (gram_product_bound Z C) hM)) (norm_nonneg _)

end RefinedBMV
