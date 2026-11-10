/- GID: D5/S3/Arith/Robin/ForwardKernel/SignedRemainder
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/SignedRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete signed Mangoldt remainder converges to its error-integral continuation. -/

import D5.S3.Arith.Robin.ForwardKernel.RemainderContinuation
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace D5.S3.Arith.Robin.ForwardKernel.SignedRemainder

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology
open ActualVonMangoldtBandCompensation (discrepancy)

private lemma signed_partial_summation {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {r dr : ℝ → ℂ}
    (hr : ∀ t ∈ Icc a b, HasDerivAt r (dr t) t)
    (hi : IntegrableOn dr (Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * r n) -
        (∫ t in a..b, r t) =
      (discrepancy b : ℂ) * r b - (discrepancy a : ℂ) * r a -
        ∫ t in a..b, (discrepancy t : ℂ) * dr t := by
  have hdr : EqOn (deriv r) dr (Icc a b) := fun t ht => (hr t ht).deriv
  have hi' : IntegrableOn (deriv r) (Icc a b) := (integrableOn_congr_fun hdr measurableSet_Icc).2 hi
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ha hab
    (fun t ht => (hr t ht).differentiableAt) hi'
  have hpsi (t : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) =
        (Chebyshev.psi t : ℂ) := by
    rw [← Complex.ofReal_sum, ← Chebyshev.psi_eq_sum_Icc]
  simp_rw [hpsi] at habel
  rw [← intervalIntegral.integral_of_le hab] at habel
  have hbody : (∫ t in a..b, deriv r t * (Chebyshev.psi t : ℂ)) =
      ∫ t in a..b, dr t * (Chebyshev.psi t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    change deriv r t * (Chebyshev.psi t : ℂ) = dr t * (Chebyshev.psi t : ℂ)
    rw [hdr ht]
  rw [hbody] at habel
  have hrcont : ContinuousOn r (Icc a b) := fun t ht => (hr t ht).continuousAt.continuousWithinAt
  have hrint : IntervalIntegrable r volume a b := hrcont.intervalIntegrable_of_Icc hab
  have hdrint : IntervalIntegrable dr volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hi
  have hpint : IntervalIntegrable (fun t : ℝ => dr t * (Chebyshev.psi t : ℂ)) volume a b := by
    have hp := integrableOn_mul_sum_Icc
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ha hi (m := 0)
    simp_rw [hpsi] at hp
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hp
  have htint : IntervalIntegrable (fun t : ℝ => dr t * (t : ℂ)) volume a b := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (hi.mul_continuousOn Complex.continuous_ofReal.continuousOn isCompact_Icc)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := r) (u' := dr) (v := fun t : ℝ => (t : ℂ)) (v' := fun _ => (1 : ℂ))
    (uIcc_of_le hab ▸ hrcont) Complex.continuous_ofReal.continuousOn
    (fun t ht => hr t (by rw [min_eq_left hab, max_eq_right hab] at ht; exact ⟨ht.1.le, ht.2.le⟩))
    (fun t _ => (hasDerivAt_id t).ofReal_comp) hdrint intervalIntegrable_const
  simp only [mul_one] at hparts
  have hdiff : (∫ t in a..b, dr t * (Chebyshev.psi t : ℂ)) -
      (∫ t in a..b, dr t * (t : ℂ)) =
        ∫ t in a..b, (discrepancy t : ℂ) * dr t := by
    rw [← intervalIntegral.integral_sub hpint htint]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [discrepancy, Complex.ofReal_sub]
    ring
  simp_rw [mul_comm (r _) (ArithmeticFunction.vonMangoldt _ : ℂ)] at habel
  rw [habel, hparts]
  simp only [discrepancy, Complex.ofReal_sub] at hdiff ⊢
  linear_combination -hdiff

/-- Partial summation preserves all prime-power atoms and identifies the
convergent signed remainder with its absolutely integrable error tail. -/
theorem signed_remainder_tendsto
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {a σ A : ℝ} (ha : 3 ≤ a) (hσ : (α - 7 / 10) < σ) (hA : 0 ≤ A)
    {r dr : ℝ → ℂ}
    (hd : ∀ t : ℝ, a ≤ t → HasDerivAt r (dr t) t)
    (hc : AEStronglyMeasurable dr (volume.restrict (Ici a)))
    (hr : ∀ t : ℝ, a ≤ t → ‖r t‖ ≤ A * t ^ (-σ - 7 / 10))
    (hdr : ∀ t : ℝ, a ≤ t → ‖dr t‖ ≤ A * t ^ (-σ - 17 / 10)) :
    Tendsto (fun b : ℝ =>
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * r n) -
        ∫ t in a..b, r t) atTop
      (𝓝 (-(discrepancy a : ℂ) * r a -
        ∫ t in Ioi a, (discrepancy t : ℂ) * dr t)) := by
  have hm : AEStronglyMeasurable dr (volume.restrict (Ioi a)) :=
    hc.mono_set Ioi_subset_Ici_self
  obtain ⟨hint, hbdry⟩ :=
    ForwardKernel.RemainderContinuation.remainder_tail_converges hα hE ha hσ hA hr hdr hm
  have hlim := (hbdry.sub_const ((discrepancy a : ℂ) * r a)).sub
    (intervalIntegral_tendsto_integral_Ioi a hint tendsto_id)
  simp only [zero_sub, neg_mul] at hlim
  rw [neg_mul]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop a] with b hb
  have hlocal : IntegrableOn dr (Icc a b) := by
    have hmaj : IntegrableOn (fun t : ℝ => A * t ^ (-σ - 17 / 10)) (Icc a b) := by
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.const_mul
      apply continuousOn_id.rpow_const
      intro t ht
      exact Or.inl (by linarith [ht.1] : t ≠ 0)
    apply hmaj.mono' (hc.mono_set Icc_subset_Ici_self)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hdr t ht.1
  exact (signed_partial_summation (by linarith : 0 ≤ a) hb
    (fun t ht => hd t ht.1) hlocal).symm

#print axioms signed_remainder_tendsto

end
end D5.S3.Arith.Robin.ForwardKernel.SignedRemainder
