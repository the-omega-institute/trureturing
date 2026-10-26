/- GID: D5/S3/Arith/Robin/MertensCumulativePeak
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/MertensCumulativePeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A cumulative second-Mertens peak yields a bounded actual lcm Robin witness. -/

import D5.S3.Arith.Robin.LcmRobinResponse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! A finite cumulative Mertens peak forces a strict Robin violation at a prefix lcm. -/

noncomputable section

open Set Finset Real MeasureTheory Filter
open scoped BigOperators Interval Topology

namespace D5.S3.Arith.Robin.ThetaTailPartialSummation

open OriginalMovingWindowMoment (weight_continuous)

private abbrev I (u : ℝ) : ℝ :=
  (Chebyshev.theta u - u) / (u * log u) - Mertens.E₂p u

private abbrev q (u : ℝ) : ℝ := u * log u / (1 + log u)
private abbrev h (u : ℝ) : ℝ := log u / (1 + log u)^2
private abbrev k (u : ℝ) : ℝ := log (log u) - 1 / log u

private abbrev w := ActualRobinClockCovariance.activationDensity
private abbrev reciprocal := ActualRobinClockCovariance.g
private abbrev g (u : ℝ) : ℝ := (Chebyshev.theta u - u) * w u

private theorem theta_mul_integrable {a b : ℝ} (ha : 2 ≤ a)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
    IntegrableOn (fun t => f t * Chebyshev.theta t) (Icc a b) := by
  simpa only [Chebyshev.theta_eq_sum_Icc, sum_filter] using
    (integrableOn_mul_sum_Icc (fun n : ℕ => if n.Prime then log n else 0)
      (show 0 ≤ a by linarith) hf (m := 0))

private theorem g_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hw : IntegrableOn w (Icc a b) :=
    (weight_continuous (b := b) (by linarith : 1 < a)).integrableOn_Icc
  have hid : IntegrableOn (fun t : ℝ => w t * t) (Icc a b) :=
    ((weight_continuous (by linarith : 1 < a)).mul continuousOn_id).integrableOn_Icc (μ := volume)
  convert (theta_mul_integrable ha hw).sub hid using 1
  ext t
  dsimp [g]
  ring

private theorem reciprocal_deriv {t : ℝ} (ht : 2 ≤ t) :
    deriv reciprocal t = -w t :=
  (ActualRobinClockCovariance.g_has_deriv_at (by linarith : 1 < t)).deriv

private theorem theta_tail_representation {u : ℝ} (hu : 2 ≤ u) :
    I u = Mertens.M + k u - ∫ t in (2 : ℝ)..u, Chebyshev.theta t * w t := by
  let c : ℕ → ℝ := fun n => if n.Prime then log n else 0
  have hc (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = Chebyshev.theta t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hs : (∑ n ∈ Icc 0 ⌊u⌋₊, reciprocal n * c n) =
      ∑ p ∈ Ioc 0 ⌊u⌋₊ with p.Prime, (1 : ℝ) / p := by
    simp only [c, mul_ite, mul_zero]
    rw [← sum_filter]
    rw [PrimorialGlobalLaplaceEnvelope.prime_filter_Icc]
    apply sum_congr rfl
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    have hl0 : log (p : ℝ) ≠ 0 :=
      (log_pos (by exact_mod_cast hpp.one_lt : (1 : ℝ) < p)).ne'
    dsimp [reciprocal, ActualRobinClockCovariance.g]
    field_simp
  have hfi : IntegrableOn (deriv reciprocal) (Icc (2 : ℝ) u) := by
    refine ((weight_continuous (by norm_num : (1 : ℝ) < 2)).neg.integrableOn_Icc (μ := volume)).congr_fun
      (fun t ht => (reciprocal_deriv ht.1).symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_integral_mul₁ c (by simp [c]) (by simp [c]) u
    (fun t ht => (ActualRobinClockCovariance.g_has_deriv_at
      (by linarith [ht.1] : 1 < t)).differentiableAt) hfi
  rw [hs, hc] at ha
  have hi : (∫ t in Ioc (2 : ℝ) u, deriv reciprocal t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) =
      -(∫ t in (2 : ℝ)..u, Chebyshev.theta t * w t) := by
    rw [← intervalIntegral.integral_of_le hu, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le hu] at ht
    change deriv reciprocal t * (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = -(Chebyshev.theta t * w t)
    rw [hc, reciprocal_deriv ht.1]
    ring
  rw [hi] at ha
  dsimp [I, Mertens.E₂p, k, reciprocal, ActualRobinClockCovariance.g] at *
  have hu0 : u ≠ 0 := by linarith
  have hl0 : log u ≠ 0 := (log_pos (by linarith : 1 < u)).ne'
  rw [ha]
  field_simp
  <;> ring

private theorem k_hasDerivAt {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt k (t * w t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : log t ≠ 0 := (log_pos (by linarith : 1 < t)).ne'
  have hd := ((Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0)).sub
    ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log ht0) hl0)
  refine hd.congr_deriv ?_
  simp only [w, ActualRobinClockCovariance.activationDensity, Function.comp_apply,
    one_mul, zero_mul, zero_sub]
  field_simp [ht0, hl0]
  <;> ring

private theorem theta_tail_finite {a u : ℝ} (ha : 2 ≤ a) (hau : a ≤ u) :
    I u = I a - ∫ t in a..u, g t := by
  have hu : 2 ≤ u := ha.trans hau
  have hkw : (∫ t in a..u, t * w t) = k u - k a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hau] at ht
      exact k_hasDerivAt (ha.trans ht.1)
    · exact (continuousOn_id.mul (weight_continuous (by linarith : 1 < a))).intervalIntegrable_of_Icc hau
  have htheta : IntervalIntegrable (fun t => Chebyshev.theta t * w t) volume (2 : ℝ) u := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hu]
    simpa only [mul_comm, MellinWeightedVariation.weight, w,
      ActualRobinClockCovariance.activationDensity] using
      theta_mul_integrable (by norm_num : (2 : ℝ) ≤ 2)
      ((weight_continuous (by norm_num : (1 : ℝ) < 2)).integrableOn_Icc (μ := volume))
  have htheta_a : IntervalIntegrable (fun t => Chebyshev.theta t * w t) volume (2 : ℝ) a := htheta.mono_set (by rw [uIcc_of_le hu, uIcc_of_le ha]; exact Icc_subset_Icc_right hau)
  have htheta_au : IntervalIntegrable (fun t => Chebyshev.theta t * w t) volume a u := htheta.mono_set
    (by rw [uIcc_of_le hu, uIcc_of_le hau]; exact Icc_subset_Icc_left ha)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals htheta_a htheta_au
  have hg : (∫ t in a..u, g t) =
      (∫ t in a..u, Chebyshev.theta t * w t) - (k u - k a) := by
    have hiu : IntervalIntegrable (fun t : ℝ => t * w t) volume a u := by
      apply ContinuousOn.intervalIntegrable_of_Icc hau
      intro t ht
      exact continuousWithinAt_id.mul (weight_continuous (by linarith : 1 < a) t ht)
    rw [← hkw, ← intervalIntegral.integral_sub htheta_au hiu]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [g]
    ring
  rw [theta_tail_representation hu, theta_tail_representation ha, hg]
  linarith

private theorem q_hasDerivAt {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt q (1 - h t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : 1 + log t ≠ 0 := by have := log_pos (by linarith : 1 < t); linarith
  have hd := ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).div
    ((hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_log ht0)) hl0
  refine hd.congr_deriv ?_
  simp only [h, Pi.add_apply, Pi.mul_apply, id_eq, one_mul, zero_add]
  field_simp [ht0, hl0]
  <;> ring

/-- Finite partial summation for the theta-tail form of the second Mertens error. -/
private theorem mertens_cumulative_partial_summation {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) :
    let I := fun u : ℝ => (Chebyshev.theta u - u) / (u * Real.log u) - Mertens.E₂p u
    let q := fun u : ℝ => u * Real.log u / (1 + Real.log u)
    let h := fun u : ℝ => Real.log u / (1 + Real.log u)^2
    IntervalIntegrable Mertens.E₂p volume a x ∧
      IntervalIntegrable (fun u => h u * I u) volume a x ∧
      (∫ u in a..x, Mertens.E₂p u) =
        q a * I a - q x * I x - ∫ u in a..x, h u * I u := by
  change IntervalIntegrable Mertens.E₂p volume a x ∧
    IntervalIntegrable (fun u => h u * I u) volume a x ∧
    (∫ u in a..x, Mertens.E₂p u) = q a * I a - q x * I x - ∫ u in a..x, h u * I u
  have hgi := g_integrable ha hax
  have hIac : AbsolutelyContinuousOnInterval I a x := by
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => I a) a x :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hp := hgi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
    apply (hc.sub hp).congr
    intro u hu
    rw [uIcc_of_le hax] at hu
    exact (theta_tail_finite ha hu.1).symm
  have hqc : ContDiffOn ℝ 1 q (uIcc a x) := by
    rw [uIcc_of_le hax]
    have ht0 : ∀ u ∈ Icc a x, u ≠ 0 := by intro u hu; linarith [hu.1]
    have hl0 : ∀ u ∈ Icc a x, 1 + log u ≠ 0 := by
      intro u hu
      have := log_pos (by linarith [hu.1] : 1 < u)
      linarith
    fun_prop (disch := aesop)
  have hqac := hqc.absolutelyContinuousOnInterval
  have hhcont : ContinuousOn h (uIcc a x) := by
    rw [uIcc_of_le hax]
    intro u hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hl0 : 1 + log u ≠ 0 := by
      have := log_pos (by linarith [hu.1] : 1 < u)
      linarith
    have hd0 : (1 + log u)^2 ≠ 0 := pow_ne_zero _ hl0
    change ContinuousWithinAt (fun v : ℝ => log v / (1 + log v)^2) (Icc a x) u
    fun_prop (disch := assumption)
  have hIint := hIac.continuousOn.intervalIntegrable (μ := volume)
  have hhIint := (hhcont.intervalIntegrable (μ := volume)).mul_continuousOn hIac.continuousOn
  have hthetaint : IntervalIntegrable
      (fun u => (Chebyshev.theta u - u) / (u * log u)) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    have hrcont : ContinuousOn reciprocal (Icc a x) := by
      intro u hu
      exact (ActualRobinClockCovariance.g_has_deriv_at
        (by linarith [hu.1] : 1 < u)).continuousAt.continuousWithinAt
    have hp := theta_mul_integrable ha (hrcont.integrableOn_Icc (μ := volume))
    have hid := (hrcont.mul continuousOn_id).integrableOn_Icc (μ := volume)
    convert hp.sub hid using 1
    ext u
    dsimp [reciprocal, ActualRobinClockCovariance.g]
    ring
  have hEint : IntervalIntegrable Mertens.E₂p volume a x := by
    convert hthetaint.sub hIint using 1
    ext u
    dsimp [I]
    ring
  refine ⟨hEint, hhIint, ?_⟩
  have hdI : ∀ᵐ u, u ∈ uIcc a x → deriv I u = -g u := by
    have hne : ∀ᵐ u : ℝ, u ≠ a ∧ u ≠ x := (volume.ae_ne a).and (volume.ae_ne x)
    filter_upwards [hgi.ae_hasDerivAt_integral, hne] with u hu hune huax
    have hder := (hasDerivAt_const u (I a)).sub (hu huax a (by simp))
    have heq : Set.EqOn (fun v => I a - ∫ t in a..v, g t) I (uIcc a x) := by
      intro v hv
      rw [uIcc_of_le hax] at hv
      exact (theta_tail_finite ha hv.1).symm
    have hu_mem : uIcc a x ∈ 𝓝 u := by
      rw [uIcc_of_le hax] at huax ⊢
      exact Icc_mem_nhds (lt_of_le_of_ne huax.1 hune.1.symm)
        (lt_of_le_of_ne huax.2 hune.2)
    exact by simpa only [zero_sub] using (hder.congr_of_eventuallyEq (heq.symm.eventuallyEq_of_mem hu_mem)).deriv
  have hparts := hqac.integral_mul_deriv_eq_deriv_mul hIac
  have hleft : (∫ u in a..x, q u * deriv I u) =
      -(∫ u in a..x, (Chebyshev.theta u - u) / (u * log u)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdI] with u hu huax
    change q u * deriv I u = -((Chebyshev.theta u - u) / (u * log u))
    rw [hu (uIoc_subset_uIcc huax)]
    rw [uIoc_of_le hax] at huax
    have hu0 : u ≠ 0 := by linarith [huax.1]
    have hl0 : log u ≠ 0 := (log_pos (by linarith [huax.1] : 1 < u)).ne'
    have hd0 : 1 + log u ≠ 0 := by have := log_pos (by linarith [huax.1] : 1 < u); linarith
    dsimp [q, g, w, ActualRobinClockCovariance.activationDensity]
    field_simp
    <;> ring
  have hright : (∫ u in a..x, deriv q u * I u) =
      (∫ u in a..x, I u) - ∫ u in a..x, h u * I u := by
    rw [← intervalIntegral.integral_sub hIint hhIint]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hax] at hu
    change deriv q u * I u = I u - h u * I u
    rw [(q_hasDerivAt (ha.trans hu.1)).deriv]
    ring
  have htheta_split : (∫ u in a..x, (Chebyshev.theta u - u) / (u * log u)) =
      (∫ u in a..x, Mertens.E₂p u) + ∫ u in a..x, I u := by
    rw [← intervalIntegral.integral_add hEint hIint]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [I]
    ring
  rw [hleft, hright, htheta_split] at hparts
  linarith

end D5.S3.Arith.Robin.ThetaTailPartialSummation

end

namespace D5.S3.Arith.Robin.MertensCumulativePeak

open Real Finset MeasureTheory
open Chebyshev
open D5.S3.Arith.Robin.PrimeFiberPropagation

noncomputable section

private theorem log_large {u : ℝ} (hu : 10000 ≤ u) : 5 < log u :=
  (OriginalFirstClockBufferEstimates.buffer_log_size
    (x := u) (z := u) (by linarith) (by linarith) (by linarith)).1

private theorem mertens_error_bounded {u : ℝ} (hu : 2 ≤ u) : |Mertens.E₂p u| ≤ 20 := by
  have h2 : log (2 : ℝ) < 1 := by linarith [Real.log_two_lt_d9]
  have h4 : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
    linarith
  have hE : Mertens.E₁ ≤ 2 := by linarith [Mertens.E₁.le]
  have hlu : (1 / 2 : ℝ) < log u :=
    lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (log_le_log (by norm_num) hu)
  exact (Mertens.E₂p.abs_le hu).trans ((div_le_iff₀ (by linarith)).mpr (by linarith))

private theorem theta_response_lower {u : ℝ} (hu : 10000 ≤ u)
    (hE : -4 / sqrt u - (psi u - u) / (u * log u) ≤ Mertens.E₃ u) :
    -6 * log u / sqrt u ≤ (theta u - u) / (u * log u) - Mertens.E₂p u := by
  have hu0 : 0 < u := by linarith
  have hlu := log_large hu
  have hs0 : 0 < sqrt u := sqrt_pos.2 hu0
  have hid : Mertens.E₃ u + Mertens.E₂p u =
      (∑ n ∈ Ioc 0 ⌊u⌋₊, Mertens.M_eq_summand n) - (Mertens.M - Mertens.γ) := by
    have hsum : (∑ n ∈ Ioc 0 ⌊u⌋₊ with n.Prime, log (1 - (1 : ℝ) / n)) +
        (∑ n ∈ Ioc 0 ⌊u⌋₊ with n.Prime, (1 : ℝ) / n) =
        ∑ n ∈ Ioc 0 ⌊u⌋₊, Mertens.M_eq_summand n := by
      rw [sum_filter, sum_filter, ← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      simp only [Mertens.M_eq_summand]
      split_ifs <;> ring
    unfold Mertens.E₃ Mertens.E₂p
    rw [Mertens.γ.eq_eulerMascheroni] at ⊢
    linarith [hsum]
  have htail := (abs_le.mp (Mertens.sum_M_eq_summand_le' (by linarith : 2 ≤ u))).2
  have herror : Mertens.E₂p u ≤
      4 / sqrt u + (psi u - u) / (u * log u) + 4 / u := by
    simp only [div_eq_mul_inv] at hE htail ⊢
    linarith [hid]
  have hgap : (psi u - theta u) / (u * log u) ≤ 2 / sqrt u := by
    apply (div_le_iff₀ (mul_pos hu0 (by linarith))).mpr
    have hg := Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ u)
    have heq : 2 / sqrt u * (u * log u) = 2 * sqrt u * log u := by
      field_simp
      nlinarith [sq_sqrt hu0.le]
    rwa [heq]
  have htail' : 4 / u ≤ 4 / sqrt u := by
    apply div_le_div_of_nonneg_left (by norm_num) hs0
    nlinarith [sq_sqrt hu0.le]
  have hraw : -(10 / sqrt u) ≤
      (theta u - u) / (u * log u) - Mertens.E₂p u := by
    have hdecomp : (theta u - u) / (u * log u) =
        (psi u - u) / (u * log u) - (psi u - theta u) / (u * log u) := by ring
    rw [hdecomp]
    simp only [div_eq_mul_inv] at herror hgap htail' ⊢
    linarith
  apply le_trans ?_ hraw
  rw [← neg_div]
  apply (div_le_div_iff_of_pos_right hs0).mpr
  linarith

private theorem initial_budget {a : ℝ} (ha : 10000 ≤ a)
    (hInt : IntervalIntegrable Mertens.E₂p volume 2 a) :
    (∫ u in (2 : ℝ)..a, Mertens.E₂p u) +
      (a * log a / (1 + log a)) * ((theta a - a) / (a * log a) - Mertens.E₂p a)
      ≤ 41 * a := by
  have ha0 : 0 < a := by linarith
  have hla := log_large ha
  have hhead : (∫ u in (2 : ℝ)..a, Mertens.E₂p u) ≤ 20 * a := by
    have hm := intervalIntegral.integral_mono_on (by linarith : (2 : ℝ) ≤ a)
      hInt (intervalIntegrable_const (c := (20 : ℝ))) (fun u hu =>
        (le_abs_self (Mertens.E₂p u)).trans (mertens_error_bounded hu.1))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    linarith
  have htheta : (theta a - a) / (a * log a) ≤ 1 := by
    have ht := Chebyshev.theta_le_log4_mul_x ha0.le
    have hl : log (4 : ℝ) ≤ log a := log_le_log (by norm_num) (by linarith)
    have hm := mul_le_mul_of_nonneg_right hl ha0.le
    apply (div_le_iff₀ (mul_pos ha0 (by linarith))).mpr
    nlinarith
  have hEa := (abs_le.mp (mertens_error_bounded (by linarith : 2 ≤ a))).1
  have hI : (theta a - a) / (a * log a) - Mertens.E₂p a ≤ 21 := by linarith
  have hq0 : 0 ≤ a * log a / (1 + log a) := by positivity
  have hqa : a * log a / (1 + log a) ≤ a :=
    (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hI hq0
  have hq := mul_le_mul_of_nonneg_left hqa (by norm_num : (0 : ℝ) ≤ 21)
  linarith

private theorem weighted_integral_bound {a x : ℝ} (ha : 10000 ≤ a) (hax : a ≤ x)
    (hE : ∀ u ∈ Set.Icc a x,
      -4 / sqrt u - (psi u - u) / (u * log u) ≤ Mertens.E₃ u)
    (hInt : IntervalIntegrable (fun u => log u / (1 + log u) ^ 2 *
      ((theta u - u) / (u * log u) - Mertens.E₂p u)) volume a x) :
    -(∫ u in a..x, log u / (1 + log u) ^ 2 *
      ((theta u - u) / (u * log u) - Mertens.E₂p u)) ≤ 12 * sqrt x := by
  have hIntR : IntervalIntegrable (fun u : ℝ => 6 / sqrt u) volume a x := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hax] at hu
    exact continuousAt_const.div (continuous_sqrt.continuousAt)
      (ne_of_gt (sqrt_pos.2 (by linarith [hu.1]))) |>.continuousWithinAt
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc a x) :
      -(log u / (1 + log u) ^ 2 *
        ((theta u - u) / (u * log u) - Mertens.E₂p u)) ≤ 6 / sqrt u := by
    have hu' : 10000 ≤ u := ha.trans hu.1
    have hlu := log_large hu'
    have hs : 0 < sqrt u := sqrt_pos.2 (by linarith)
    have hw : 0 ≤ log u / (1 + log u) ^ 2 := by positivity
    have hlower := mul_le_mul_of_nonneg_left (theta_response_lower hu' (hE u hu)) hw
    have hweight : (log u / (1 + log u) ^ 2) * (6 * log u / sqrt u) ≤ 6 / sqrt u := by
      have hden : 0 < (1 + log u) ^ 2 := sq_pos_of_pos (by linarith)
      apply (le_div_iff₀ hs).mpr
      field_simp
      nlinarith
    have heq : (log u / (1 + log u) ^ 2) * (-6 * log u / sqrt u) =
        -((log u / (1 + log u) ^ 2) * (6 * log u / sqrt u)) := by ring
    rw [heq] at hlower
    linarith
  have hm := intervalIntegral.integral_mono_on hax hInt.neg hIntR hpoint
  simp only [Pi.neg_apply] at hm
  rw [intervalIntegral.integral_neg] at hm
  have hprimitive : (∫ u in a..x, 6 / sqrt u) = 12 * sqrt x - 12 * sqrt a := by
    calc
      _ = 6 * ∫ u in a..x, u ^ (-(1 / 2) : ℝ) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hax] at hu
        change 6 / sqrt u = 6 * u ^ (-(1 / 2) : ℝ)
        rw [Real.rpow_neg (by linarith [hu.1] : 0 ≤ u)]
        simp [Real.sqrt_eq_rpow, div_eq_mul_inv]
      _ = 12 * sqrt x - 12 * sqrt a := by
        rw [integral_rpow (r := -(1 / 2 : ℝ)) (Or.inl (by norm_num))]
        norm_num [← Real.sqrt_eq_rpow]
        <;> ring
  rw [hprimitive] at hm
  linarith [sqrt_nonneg a]

private theorem cumulative_bound {x : ℝ} (hx : (10000 : ℝ) ^ 2 ≤ x)
    (hE : ∀ u ∈ Set.Icc (10000 : ℝ) x,
      -4 / sqrt u - (psi u - u) / (u * log u) ≤ Mertens.E₃ u) :
    (∫ u in (2 : ℝ)..x, Mertens.E₂p u) ≤ 12 * sqrt x * log x := by
  have hx0 : 0 < x := by nlinarith
  have hax : (10000 : ℝ) ≤ x := by nlinarith
  have hlx := log_large hax
  have hsx : 0 < sqrt x := sqrt_pos.2 hx0
  have hsa : (10000 : ℝ) ≤ sqrt x := Real.le_sqrt_of_sq_le hx
  have hlogx : 10 < log x := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 10000 ^ 2) hx
    rw [log_pow] at h
    norm_num at h
    linarith [log_large (show (10000 : ℝ) ≤ 10000 by rfl)]
  have hbase := ThetaTailPartialSummation.mertens_cumulative_partial_summation
    (a := (2 : ℝ)) (x := 10000) (by norm_num) (by norm_num)
  have hsegment := ThetaTailPartialSummation.mertens_cumulative_partial_summation
    (a := (10000 : ℝ)) (x := x) (by norm_num) hax
  dsimp only at hbase hsegment
  obtain ⟨hInt0, _, _⟩ := hbase
  obtain ⟨hInt1, hIntH, hidentity⟩ := hsegment
  have hhead := initial_budget (show (10000 : ℝ) ≤ 10000 by rfl) hInt0
  have htail := weighted_integral_bound (show (10000 : ℝ) ≤ 10000 by rfl) hax hE hIntH
  have hIx := theta_response_lower hax (hE x ⟨hax, le_rfl⟩)
  have hq0 : 0 ≤ x * log x / (1 + log x) := by positivity
  have hqx : x * log x / (1 + log x) ≤ x :=
    (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have hend : -(x * log x / (1 + log x) *
      ((theta x - x) / (x * log x) - Mertens.E₂p x)) ≤ 6 * sqrt x * log x := by
    have hlow := mul_le_mul_of_nonneg_left hIx hq0
    have hupper := mul_le_mul_of_nonneg_right hqx
      (show 0 ≤ 6 * log x / sqrt x by positivity)
    have heq : x * (6 * log x / sqrt x) = 6 * sqrt x * log x := by
      field_simp
      nlinarith [sq_sqrt hx0.le]
    have hneg : x * log x / (1 + log x) * (-6 * log x / sqrt x) =
        -(x * log x / (1 + log x) * (6 * log x / sqrt x)) := by ring
    rw [heq] at hupper
    rw [hneg] at hlow
    linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1
  have hfull : (∫ u in (2 : ℝ)..x, Mertens.E₂p u) ≤
      41 * 10000 + 6 * sqrt x * log x + 12 * sqrt x := by
    linarith [hidentity]
  have hstrict : 41 * 10000 + 6 * sqrt x * log x + 12 * sqrt x <
      12 * sqrt x * log x := by
    have hlarge := mul_pos hsx (show 0 < 6 * log x - 53 by linarith)
    nlinarith
  exact hfull.trans hstrict.le

/-- A large cumulative second-Mertens error yields an actual bounded strict Robin witness. -/
theorem mertens_cumulative_peak_robin_witness {x : ℝ} (hx : (10000 : ℝ) ^ 2 ≤ x)
    (hpeak : 12 * Real.sqrt x * Real.log x < ∫ t in (2 : ℝ)..x, Mertens.E₂p t) :
    ∃ t ∈ Set.Icc (10000 : ℝ) x,
      let N := Nat.lcmUpto ⌊t⌋₊
      5040 < N ∧ (N : ℝ) ≤ Real.exp (x * Real.log x) ∧
      divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) := by
  classical
  have hex : ∃ t ∈ Set.Icc (10000 : ℝ) x,
      Mertens.E₃ t < -4 / sqrt t - (psi t - t) / (t * log t) := by
    by_contra hn
    push_neg at hn
    exact (not_le_of_gt hpeak) (cumulative_bound hx hn)
  obtain ⟨t, ht, hE⟩ := hex
  have hw := LcmRobinResponse.common_robin_response ht.1 hE
  dsimp only at hw
  refine ⟨t, ht, hw.2.1, hw.2.2.2.trans ?_, hw.1⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul ht.2 (log_le_log (by linarith [ht.1]) ht.2)
    (log_nonneg (by linarith [ht.1])) (by nlinarith [hx] : 0 ≤ x)

end
end D5.S3.Arith.Robin.MertensCumulativePeak
