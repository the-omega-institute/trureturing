/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted occupation estimates for the finite bilinear squeezed vacuum. -/

import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
The coefficients and factorial weights are the native polynomial Gaussian
coefficients and factorial Fock weights. Pairings in this module are bilinear;
there is no complex conjugation. The finite mode type may be empty.

The intended vacuum identity is the classical squeezed Gaussian/Bargmann-Wick
identity. Finite field sewing, Gram transport, countable limits and physical
realization are separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum

open MvPolynomial
open FactorialFockQuadraticEstimate
open FactorialFockMetric (weight)

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

private theorem quadratic_smul (A : Matrix I I ℂ) (c : ℂ) :
    quadratic (c • A) = c • quadratic A := by
  simp only [quadratic, Matrix.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, smul_smul]
  congr 1
  ring

private theorem gaussianCoefficient_smul (A : Matrix I I ℂ) (c : ℂ) (d : I →₀ ℕ) :
    gaussianCoefficient (c • A) d = c ^ (d.degree / 2) * gaussianCoefficient A d := by
  simp only [gaussianCoefficient, gaussianPiece, quadratic_smul, smul_pow,
    coeff_smul, smul_eq_mul]
  ring

private theorem polynomial_geometric_bound {s : ℝ} (hs : 1 < s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n + 1 : ℝ) ^ k ≤ C * s ^ n := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hr : ‖s⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
                            exact inv_lt_one_of_one_lt₀ hs
  have hsum := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr
  let T : ℝ := ∑' n : ℕ, (n : ℝ) ^ k * (s⁻¹) ^ n
  have hT : 0 ≤ T := tsum_nonneg (fun n => by positivity)
  refine ⟨s * T, mul_nonneg hs0.le hT, ?_⟩
  intro n
  have hn : (n + 1 : ℝ) ^ k * (s⁻¹) ^ (n + 1) ≤ T := by
    exact hsum.le_tsum (n + 1) (fun m _ => by positivity)
  have hh := mul_le_mul_of_nonneg_right hn (pow_nonneg hs0.le (n + 1))
  simpa only [mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow, mul_one,
    pow_succ, ← mul_assoc, mul_comm T s] using hh

/-- Every fixed polynomial occupation weight is summable for the actual
Gaussian coefficients of a symmetric strict Euclidean contraction. -/
theorem weighted_occupation_summable (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) (k : ℕ) :
    Summable (fun d : I →₀ ℕ => (d.degree + 1 : ℝ) ^ k *
      (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2) := by
  let a : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
  have ha : 0 ≤ a := norm_nonneg _
  let c : ℝ := 2 / (1 + a)
  have hden : 0 < 1 + a := by positivity
  have hc : 1 < c := (lt_div_iff₀ hden).2 (by dsimp [a]; linarith)
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hca : c * a < 1 := by
    dsimp [c]
    rw [div_mul_eq_mul_div, div_lt_one hden]
    dsimp [a]
    linarith
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((c : ℂ) • A)‖ = c * a := by
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hscaled := occupation_summable ((c : ℂ) • A)
    (fun i j => by simp only [Matrix.smul_apply]; rw [hsym i j])
    (mul_nonneg hc0.le ha) hca hnorm.le
  obtain ⟨C, hC, hbound⟩ := polynomial_geometric_bound (show 1 < c ^ 2 by nlinarith) k
  apply Summable.of_nonneg_of_le (fun d => by positivity)
    (g := fun d : I →₀ ℕ => (2 : ℝ) ^ k * C *
      ((weight d : ℝ) * ‖gaussianCoefficient ((c : ℂ) • A) d‖ ^ 2))
    _ (hscaled.mul_left _)
  intro d
  by_cases hodd : d.degree % 2 = 1
  · simp only [gaussianCoefficient_odd A d hodd, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero]
    positivity
  · have heven : d.degree = 2 * (d.degree / 2) := by omega
    have hp : (d.degree + 1 : ℝ) ^ k ≤ (2 : ℝ) ^ k *
        (C * (c ^ 2) ^ (d.degree / 2)) := by
      calc
        _ ≤ (2 * (d.degree / 2 + 1 : ℝ)) ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          have hh : (d.degree : ℝ) = 2 * (d.degree / 2 : ℕ) := by exact_mod_cast heven
          linarith
        _ = (2 : ℝ) ^ k * (d.degree / 2 + 1 : ℝ) ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound _) (by positivity)
    rw [gaussianCoefficient_smul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc0]
    have hh := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2 by positivity)
    convert hh using 1 <;> ring

end D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
