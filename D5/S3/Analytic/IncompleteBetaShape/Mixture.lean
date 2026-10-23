/- GID: D5/S3/Analytic/IncompleteBetaShape/Mixture
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBetaShape/Mixture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Beta mixture representation of the first parameter coefficient convolution. -/

import D5.S3.Analytic.IncompleteBetaShape.Defs
import D5.S3.Analytic.KummerRatio.BetaIntegral

noncomputable section

open Set MeasureTheory
open D5.S3.Analytic.IncompleteBeta
open D5.S3.Analytic.KummerRatio.BetaIntegral

namespace D5.S3.Analytic.IncompleteBetaShape.Mixture

def convolution (p q b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), coeff p b k * coeff q b (n - k)

/-- The uniform mixture of the beta densities with shapes
`p+k+1` and `q+n-k+1`, for `k` from zero through `n`. -/
def mixtureDensity (p q : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.Gamma (p + q + n + 2) / (n + 1) *
    ∑ k ∈ Finset.range (n + 1),
      y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1))

/-- The positive prefactor depends on the two shape parameters only through their sum. -/
def mixtureFactor (c : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  (n + 1) * Real.Gamma (c + n + 2 * b) /
    (Real.Gamma b ^ 2 * Real.Gamma (c + n + 2))

/-- The coefficient convolution is a beta-mixture mean of the symmetric power weight. -/
theorem convolution_eq_mixtureMean {p q b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b) (n : ℕ) :
    convolution p q b n = mixtureFactor (p + q) n b *
      ∫ y in (0 : ℝ)..1, (y * (1 - y)) ^ (b - 1) * mixtureDensity p q n y := by
  let F := fun k : ℕ => fun y : ℝ =>
    (y * (1 - y)) ^ (b - 1) *
      (y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)))
  have he (k : ℕ) (y : ℝ) (hy : y ∈ Ioo 0 1) :
      F k y = y ^ (p + b + k - 1) * (1 - y) ^ (q + b + (n - k : ℕ) - 1) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by
    dsimp only [F]
    rw [Real.mul_rpow hy.1.le (sub_pos.mpr hy.2).le]
    calc
      _ = (y ^ (b - 1) * y ^ (p + k)) *
          ((1 - y) ^ (b - 1) * (1 - y) ^ (q + (n - k : ℕ))) /
            (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hy.1, ← Real.rpow_add (sub_pos.mpr hy.2)]
        congr 3 <;> ring
  have hi (k : ℕ) (_hk : k ∈ Finset.range (n + 1)) :
      IntervalIntegrable (F k) volume 0 1 := by
    apply ((intervalIntegrable_beta (by positivity : 0 < p + b + k)
      (by positivity : 0 < q + b + (n - k : ℕ))).div_const
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1))).congr_uIoo
    intro y hy
    rw [uIoo_of_le zero_le_one] at hy
    exact (he k y hy).symm
  have ht (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Real.Gamma (p + q + n + 2 * b) / Real.Gamma b ^ 2 *
        (∫ y in (0 : ℝ)..1, F k y) = coeff p b k * coeff q b (n - k) := by
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsum : p + b + k + (q + b + (n - k : ℕ)) = p + q + n + 2 * b := by
      rw [Nat.cast_sub hk']
      ring
    have hI : (∫ y in (0 : ℝ)..1, F k y) =
        (Real.Gamma (p + b + k) * Real.Gamma (q + b + (n - k : ℕ)) /
          Real.Gamma (p + q + n + 2 * b)) /
            (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by
      calc
        _ = ∫ y in (0 : ℝ)..1,
            (y ^ (p + b + k - 1) * (1 - y) ^ (q + b + (n - k : ℕ) - 1)) /
              (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) :=
          intervalIntegral.integral_congr_Ioo_of_le zero_le_one (fun y hy => he k y hy)
        _ = _ := by
          rw [intervalIntegral.integral_div,
            integral_beta (by positivity : 0 < p + b + k)
              (by positivity : 0 < q + b + (n - k : ℕ)), hsum]
    rw [hI]
    unfold coeff
    have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < p + q + n + 2 * b)).ne'
    field_simp (disch := assumption)
    <;> ring
  have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < p + q + n + 2)).ne'
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hrewrite :
      (fun y => (y * (1 - y)) ^ (b - 1) * mixtureDensity p q n y) =
      (fun y => (Real.Gamma (p + q + n + 2) / (n + 1)) *
        ∑ k ∈ Finset.range (n + 1), F k y) := by
    funext y
    simp only [mixtureDensity, F, Finset.mul_sum]
    ring
  rw [hrewrite, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum hi]
  have hfactor : mixtureFactor (p + q) n b *
      (Real.Gamma (p + q + n + 2) / (n + 1)) =
      Real.Gamma (p + q + n + 2 * b) / Real.Gamma b ^ 2 := by
    unfold mixtureFactor
    field_simp (disch := assumption)
  rw [← mul_assoc, hfactor, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k hk => (ht k hk).symm)

end D5.S3.Analytic.IncompleteBetaShape.Mixture
