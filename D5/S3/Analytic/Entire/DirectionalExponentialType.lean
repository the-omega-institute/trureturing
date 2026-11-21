/- GID: D5/S3/Analytic/Entire/DirectionalExponentialType
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/DirectionalExponentialType
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadrant bounds turn radial exponential growth into directional growth. -/

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Directional exponential type -/

open Set Filter Asymptotics Complex Bornology

namespace D5.S3.Analytic.Entire

/-- Real-axis boundedness turns a radial exponential bound into a directional one,
with the same exponential type and polynomial order. -/
theorem norm_le_exp_abs_im {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a B C : ℝ} {m : ℕ} (ha : 0 ≤ a)
    (hreal : ∀ x : ℝ, ‖F (x : ℂ)‖ ≤ B)
    (hradial : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * ‖z‖)) :
    ∀ z : ℂ, ‖F z‖ ≤ max B C * (1 + ‖z‖) ^ m * Real.exp (a * |z.im|) := by
  let D (s : ℝ) (z : ℂ) := 1 - (s : ℂ) * I * z
  let H (s : ℝ) (z : ℂ) :=
    F z * Complex.exp (((a * s : ℝ) : ℂ) * I * z) / D s z ^ m
  have hDre (s : ℝ) (z : ℂ) : (D s z).re = 1 + s * z.im := by
    simp [D, Complex.mul_re, Complex.mul_im]
  have hDlower (s : ℝ) (z : ℂ) (hz : 0 ≤ s * z.im) : 1 ≤ ‖D s z‖ :=
    (show 1 ≤ (D s z).re by rw [hDre]; linarith).trans (Complex.re_le_norm _)
  have hDupper (s : ℝ) (hs : |s| = 1) (z : ℂ) : ‖D s z‖ ≤ 1 + ‖z‖ := by
    simpa only [D, norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hs, one_mul] using norm_sub_le (1 : ℂ) ((s : ℂ) * I * z)
  have hHnorm (s : ℝ) (z : ℂ) :
      ‖H s z‖ = ‖F z‖ * Real.exp (-(a * (s * z.im))) / ‖D s z‖ ^ m := by
    simp only [H, norm_div, norm_mul, norm_pow, Complex.norm_exp, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, I_re, I_im]
    ring_nf
  have hdiff (s : ℝ) :
      DiffContOnCl ℂ (H s) {z : ℂ | 0 < s * z.im} := by
    have hclosed : IsClosed {z : ℂ | 0 ≤ s * z.im} :=
      isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)
    have hne : ∀ z ∈ closure {z : ℂ | 0 < s * z.im}, D s z ^ m ≠ 0 := by
      intro z hz
      have hsub : {z : ℂ | 0 < s * z.im} ⊆ {z : ℂ | 0 ≤ s * z.im} := by
        intro w hw
        exact le_of_lt (show 0 < s * w.im from hw)
      have hle := closure_minimal hsub hclosed hz
      exact pow_ne_zero _ (norm_pos_iff.1 (zero_lt_one.trans_le (hDlower s z hle)))
    have hnum : Differentiable ℂ (fun z : ℂ => F z *
        Complex.exp (((a * s : ℝ) : ℂ) * I * z)) := by fun_prop
    have hden : Differentiable ℂ (fun z => D s z ^ m) := by dsimp [D]; fun_prop
    exact ⟨hnum.differentiableOn.div hden.differentiableOn
      (fun z hz => hne z (subset_closure hz)),
      hnum.continuous.continuousOn.div hden.continuous.continuousOn hne⟩
  have hHreal (s x : ℝ) : ‖H s (x : ℂ)‖ ≤ max B C := by
    rw [hHnorm, Complex.ofReal_im, mul_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact (div_le_self (norm_nonneg _)
      (one_le_pow₀ (hDlower s (x : ℂ) (by simp)))).trans
        ((hreal x).trans (le_max_left _ _))
  have hHim (s x : ℝ) (hsx : s * x = |x|) :
      ‖H s ((x : ℂ) * I)‖ ≤ max B C := by
    have hden : D s ((x : ℂ) * I) = ((1 + s * x : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hDre]
      · simp [D, Complex.mul_im, Complex.mul_re]
    have hnorm : ‖(x : ℂ) * I‖ = |x| := by simp [Real.norm_eq_abs]
    rw [hHnorm, Complex.mul_I_im, Complex.ofReal_re, hden, Complex.norm_real,
      Real.norm_eq_abs, hsx, abs_of_nonneg (by positivity : 0 ≤ 1 + |x|)]
    apply le_trans _ (le_max_right B C)
    calc
      _ ≤ C * (1 + |x|) ^ m * Real.exp (a * |x|) * Real.exp (-(a * |x|)) /
          (1 + |x|) ^ m := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by simpa only [hnorm] using hradial ((x : ℂ) * I))
          (Real.exp_pos _).le
      _ = C := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one,
          mul_div_cancel_right₀ _ (by positivity)]
  have hC : 0 ≤ C := by simpa using (norm_nonneg (F 0)).trans (hradial 0)
  have hgrowth (s : ℝ) (t : Set ℂ) (ht : ∀ z ∈ t, 0 ≤ s * z.im) :
      ∃ c < (2 : ℝ), ∃ b : ℝ,
        H s =O[cobounded ℂ ⊓ 𝓟 t] (fun z => Real.exp (b * ‖z‖ ^ c)) := by
    refine ⟨1, by norm_num, a + m, IsBigO.of_bound C ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun z hz => ?_)
    simp only [Real.rpow_one, Real.norm_eq_abs, Real.abs_exp]
    have hexp : Real.exp (-(a * (s * z.im))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha (ht z hz)))
    have hpow : (1 + ‖z‖) ^ m ≤ Real.exp ((m : ℝ) * ‖z‖) := by
      rw [Real.exp_nat_mul]
      have hbase : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by
        simpa only [add_comm] using (Real.add_one_le_exp ‖z‖)
      exact pow_le_pow_left₀ (by positivity) hbase _
    calc
      ‖H s z‖ ≤ ‖F z‖ := by
        rw [hHnorm]
        exact (div_le_self (by positivity) (one_le_pow₀ (hDlower s z (ht z hz)))).trans
          (mul_le_of_le_one_right (norm_nonneg _) hexp)
      _ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * ‖z‖) := hradial z
      _ ≤ C * Real.exp ((m : ℝ) * ‖z‖) * Real.exp (a * ‖z‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (Real.exp_pos _).le
      _ = C * Real.exp ((a + m) * ‖z‖) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hupper (z : ℂ) (hz : 0 ≤ z.im) : ‖H 1 z‖ ≤ max B C := by
    have haxis (x : ℝ) (hx : 0 ≤ x) := hHim 1 x (by rw [one_mul, abs_of_nonneg hx])
    rcases le_total 0 z.re with hre | hre
    · exact PhragmenLindelof.quadrant_I
        ((hdiff 1).mono fun w hw => by
          simpa only [mem_ofPred_eq, one_mul, mem_Ioi] using (Complex.mem_reProdIm.mp hw).2)
        (hgrowth 1 _ fun w hw => by
          rw [one_mul]
          exact le_of_lt (show 0 < w.im from (Complex.mem_reProdIm.mp hw).2))
        (fun x _ => hHreal 1 x) haxis hre hz
    · exact PhragmenLindelof.quadrant_II
        ((hdiff 1).mono fun w hw => by
          simpa only [mem_ofPred_eq, one_mul, mem_Ioi] using (Complex.mem_reProdIm.mp hw).2)
        (hgrowth 1 _ fun w hw => by
          rw [one_mul]
          exact le_of_lt (show 0 < w.im from (Complex.mem_reProdIm.mp hw).2))
        (fun x _ => hHreal 1 x) haxis hre hz
  have hlower (z : ℂ) (hz : z.im ≤ 0) : ‖H (-1) z‖ ≤ max B C := by
    have haxis (x : ℝ) (hx : x ≤ 0) := hHim (-1) x (by rw [neg_one_mul, abs_of_nonpos hx])
    rcases le_total z.re 0 with hre | hre
    · exact PhragmenLindelof.quadrant_III
        ((hdiff (-1)).mono fun w hw => by
          simpa only [mem_ofPred_eq, neg_one_mul, neg_pos, mem_Iio] using
            (Complex.mem_reProdIm.mp hw).2)
        (hgrowth (-1) _ fun w hw => by
          rw [neg_one_mul, neg_nonneg]
          exact le_of_lt (show w.im < 0 from (Complex.mem_reProdIm.mp hw).2))
        (fun x _ => hHreal (-1) x) haxis hre hz
    · exact PhragmenLindelof.quadrant_IV
        ((hdiff (-1)).mono fun w hw => by
          simpa only [mem_ofPred_eq, neg_one_mul, neg_pos, mem_Iio] using
            (Complex.mem_reProdIm.mp hw).2)
        (hgrowth (-1) _ fun w hw => by
          rw [neg_one_mul, neg_nonneg]
          exact le_of_lt (show w.im < 0 from (Complex.mem_reProdIm.mp hw).2))
        (fun x _ => hHreal (-1) x) haxis hre hz
  intro z
  obtain ⟨s, hs, hsz, hbound⟩ : ∃ s : ℝ, |s| = 1 ∧ s * z.im = |z.im| ∧
      ‖H s z‖ ≤ max B C := by
    rcases le_total 0 z.im with hz | hz
    · exact ⟨1, abs_one, by rw [one_mul, abs_of_nonneg hz], hupper z hz⟩
    · exact ⟨-1, by simp, by rw [neg_one_mul, abs_of_nonpos hz], hlower z hz⟩
  have hdpos : 0 < ‖D s z‖ ^ m := by
    apply pow_pos (zero_lt_one.trans_le (hDlower s z _))
    rw [hsz]
    exact abs_nonneg _
  rw [hHnorm, hsz, div_le_iff₀ hdpos, Real.exp_neg, ← div_eq_mul_inv,
    div_le_iff₀ (Real.exp_pos _)] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hDupper s hs z) m)
      (hC.trans (le_max_right _ _))) (Real.exp_pos _).le)

end D5.S3.Analytic.Entire
