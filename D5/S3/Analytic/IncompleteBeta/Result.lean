/- GID: D5/S3/Analytic/IncompleteBeta/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBeta/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.NatAntidiagonal]
   utility: none
   digest: The incomplete beta Turanian has strictly positive coefficients. -/

import D5.S3.Analytic.IncompleteBeta.Comparison
import D5.S3.Analytic.IncompleteBeta.Moment
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
The pinned `phi a b α β n` is the coefficient of `x^n` in
`x^(-2*a) * (1-x)^(-2*b-α-β)` times
`I_x(a,b+α) * I_x(a,b+β) - I_x(a,b) * I_x(a,b+α+β)`, by equations
(1), (3), and (4) of the normalized incomplete beta source. The coefficients
are independent of `x`, so its restriction to `(0,1)` adds no coefficient condition.

A fixed sum of beta shapes gives a common positive moment factor.
-/

noncomputable section
open Set MeasureTheory
open D5.S3.Analytic.IncompleteBeta.Comparison
open D5.S3.Analytic.IncompleteBeta.Moment

namespace D5.S3.Analytic.IncompleteBeta.Result

private lemma convolution_symm (a s t : ℝ) (n : ℕ) :
    convolution a s t n = convolution a t s n := by
  have H := Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun p : ℕ × ℕ => coeff a s p.1 * coeff a t p.2)
  change (∑ p ∈ Finset.antidiagonal n, coeff a s p.2 * coeff a t p.1) =
    ∑ p ∈ Finset.antidiagonal n, coeff a s p.1 * coeff a t p.2 at H
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at H
  unfold convolution
  exact H.symm.trans (Finset.sum_congr rfl (fun k _ => mul_comm _ _))

/-- At fixed positive mean shape, the coefficient convolution strictly decreases
with the nonnegative half-difference of its two shape parameters. -/
theorem convolution_strictAnti_imbalance {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (n : ℕ) :
    StrictAntiOn (fun d => convolution a (m + d) (m - d) n) (Ico 0 m) := by
  have hW : ContinuousOn (W a n) (Icc 0 1) := W_continuousOn ha n
  have hsymm : ∀ u ∈ Icc 0 1, W a n (1 - u) = W a n u :=
    fun u _ => W_symm n u
  have hmono : StrictMonoOn (W a n) (Ioc 0 (1 / 2)) :=
    (W_strictMonoOn ha n).mono Ioc_subset_Icc_self
  have H := betaMean_strictAntiOn hW hsymm hmono hm
  have hG : 0 < Real.Gamma (2 * a + 2 * m + n) / Real.Gamma (2 * m) :=
    div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  have hEq (d : ℝ) (hd : d ∈ Ico 0 m) :
      convolution a (m + d) (m - d) n =
        (Real.Gamma (2 * a + 2 * m + n) / Real.Gamma (2 * m)) *
          betaMean (W a n) m d := by
    have hp : 0 < m + d := by linarith [hd.1]
    have hq : 0 < m - d := sub_pos.mpr hd.2
    have hgp := (Real.Gamma_pos_of_pos hp).ne'
    have hgq := (Real.Gamma_pos_of_pos hq).ne'
    have hgm := (Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < 2 * m)).ne'
    rw [convolution_eq_betaMean ha hp hq]
    unfold betaMean
    rw [show 2 * a + (m + d) + (m - d) + (n:ℝ) = 2 * a + 2 * m + n by ring]
    field_simp (disch := assumption)
  intro d hd e he hde
  change convolution a (m + e) (m - e) n < convolution a (m + d) (m - d) n
  rw [hEq d hd, hEq e he]
  exact mul_lt_mul_of_pos_left (H hd he hde) hG

/-- Every Turanian coefficient is strictly positive for positive real parameters. -/
theorem result : claim := by
  intro a b α β ha hb hα hβ n
  let m := b + (α + β) / 2
  let d := |α - β| / 2
  let e := (α + β) / 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hde : d < e := by
    dsimp [d, e]
    have H : |α - β| < α + β := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have he : e ∈ Ico 0 m := by
    dsimp [e, m]
    constructor <;> linarith
  have hd : d ∈ Ico 0 m := ⟨by dsimp [d]; positivity, hde.trans he.2⟩
  have H := convolution_strictAnti_imbalance ha hm n hd he hde
  have hleft : convolution a (m + e) (m - e) n = convolution a b (b + α + β) n := by
    have hp : m + e = b + α + β := by dsimp [m, e]; ring
    have hq : m - e = b := by dsimp [m, e]; ring
    rw [hp, hq, convolution_symm]
  have hright : convolution a (m + d) (m - d) n =
      convolution a (b + α) (b + β) n := by
    rcases le_total β α with hβα | hαβ
    · have hp : m + d = b + α := by
        dsimp [m, d]
        rw [abs_of_nonneg (sub_nonneg.mpr hβα)]
        ring
      have hq : m - d = b + β := by
        dsimp [m, d]
        rw [abs_of_nonneg (sub_nonneg.mpr hβα)]
        ring
      rw [hp, hq]
    · have hp : m + d = b + β := by
        dsimp [m, d]
        rw [abs_of_nonpos (sub_nonpos.mpr hαβ)]
        ring
      have hq : m - d = b + α := by
        dsimp [m, d]
        rw [abs_of_nonpos (sub_nonpos.mpr hαβ)]
        ring
      rw [hp, hq, convolution_symm]
  change convolution a (m + e) (m - e) n < convolution a (m + d) (m - d) n at H
  rw [hleft, hright] at H
  unfold phi
  rw [Finset.sum_sub_distrib]
  exact sub_pos.mpr H

end D5.S3.Analytic.IncompleteBeta.Result
