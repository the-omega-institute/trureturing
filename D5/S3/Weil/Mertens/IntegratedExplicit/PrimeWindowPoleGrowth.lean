/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A right-half-strip zero forces positive Mangoldt mass on every sufficiently late power window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth

private def coeff (k : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ)^k / k.factorial) * iteratedDeriv k CompleteMangoldtLaurent.transform s

private def weight (k : ℕ) (σ u : ℝ) : ℝ :=
  u^k * Real.exp (-(σ*u)) / k.factorial

private def integrand (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ)^k * Complex.exp (-s*u) * (U (Real.exp u) : ℂ) / k.factorial

private lemma coeff_integral (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (integrand k s) (Ioi 0) ∧
      coeff k s = ∫ u in Ioi 0, integrand k s u := by
  obtain ⟨hi, heq⟩ := CompleteMangoldtMoments.iterated_derivative_moment k hs
  let q := (-1 : ℂ)^k / k.factorial
  have hh (u : ℝ) : q * ((-(u : ℂ))^k *
      (Complex.exp (-s*u) * (U (Real.exp u) : ℂ))) = integrand k s u := by
    have hsquare : (-1 : ℂ)^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    rw [show -(u : ℂ) = (-1 : ℂ)*u by ring, mul_pow]
    unfold q integrand
    linear_combination ((u : ℂ)^k * Complex.exp (-s*u) * (U (Real.exp u) : ℂ) /
      k.factorial) * hsquare
  refine ⟨(hi.const_mul q).congr (ae_of_all _ hh), ?_⟩
  unfold coeff
  rw [heq, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ hh)

private lemma norm_integrand (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖integrand k s u‖ = |U (Real.exp u)| * weight k s.re u := by
  simp [integrand, weight, norm_pow, Complex.norm_exp,
    Complex.mul_re, abs_of_nonneg hu]
  ring

private lemma real_integrand (k : ℕ) (σ u : ℝ) :
    integrand k (σ : ℂ) u = ((U (Real.exp u) * weight k σ u : ℝ) : ℂ) := by
  unfold integrand weight
  push_cast
  rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  push_cast
  ring

private lemma positive_moment (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖coeff k s‖ + (coeff k (s.re : ℂ)).re ≤
      ∫ u in Ioi 0, 2 * max (U (Real.exp u)) 0 * weight k s.re u := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  obtain ⟨hi, heq⟩ := coeff_integral k hs
  obtain ⟨hj, hre⟩ := coeff_integral k (s := (s.re : ℂ)) (by simpa)
  have hreal : Integrable (fun u => U (Real.exp u) * weight k s.re u) μ := by
    have hcast := hj.congr (ae_of_all _ fun u => real_integrand k s.re u)
    simpa using hcast.re
  have heqreal : (coeff k (s.re : ℂ)).re =
      ∫ u, U (Real.exp u) * weight k s.re u ∂μ := by
    rw [hre, integral_congr_ae (ae_of_all _ fun u => real_integrand k s.re u),
      integral_complex_ofReal]
    rfl
  rw [heq, heqreal]
  calc
    _ ≤ (∫ u, ‖integrand k s u‖ ∂μ) + ∫ u, U (Real.exp u) * weight k s.re u ∂μ :=
      add_le_add (norm_integral_le_integral_norm _) le_rfl
    _ = _ := by
      rw [← integral_add hi.norm hreal]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
      rw [norm_integrand k s (le_of_lt hu), ← add_mul]
      congr 1
      rcases le_total 0 (U (Real.exp u)) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring


private lemma weight_le (k : ℕ) {σ u : ℝ} (hσ : 1 < σ) (hu : 0 ≤ u) :
    weight k σ u ≤ (σ-1/2)⁻¹^k * Real.exp (-(u/2)) := by
  have hr : 0 < σ-1/2 := by linarith
  have h := Real.pow_div_factorial_le_exp ((σ-1/2)*u) (mul_nonneg hr.le hu) k
  rw [mul_pow] at h
  have hf : 0 < (k.factorial : ℝ) := by positivity
  have h1 : u^k / k.factorial ≤ (σ-1/2)⁻¹^k * Real.exp ((σ-1/2)*u) := by
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hr k)]
    simpa only [div_mul_eq_mul_div, mul_comm] using h
  calc
    weight k σ u = u^k / k.factorial * Real.exp (-(σ*u)) := by unfold weight; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans_eq (by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring)

/-- The total absolute moment outside the window stays as an explicit error.
The arithmetic term inside it uses just the positive part of the complete
Mangoldt remainder. -/
private lemma coeff_window (k : ℕ) {s : ℂ} (hs : 1 < s.re) {a z : ℝ} (ha : 0 < a) :
    ‖coeff k s‖ + (coeff k (s.re : ℂ)).re ≤
      2 * ((s.re-1/2)⁻¹^k *
        (∫ u in Icc a z, max (U (Real.exp u)) 0 * Real.exp (-(u/2))) +
        ∫ u in Ioi (0 : ℝ) \ Icc a z, |U (Real.exp u)| * weight k s.re u) := by
  let g (u : ℝ) := U (Real.exp u)
  let f (u : ℝ) := max (g u) 0 * weight k s.re u
  let F (u : ℝ) := |g u| * weight k s.re u
  let j (u : ℝ) := max (g u) 0 * Real.exp (-(u/2))
  have hg : Continuous g := U_exp_continuous
  have hw : Continuous (weight k s.re) := by unfold weight; fun_prop
  have hfC : Continuous f := (hg.max continuous_const).mul hw
  have hjC : Continuous j := (hg.max continuous_const).mul (by fun_prop)
  have hw0 {u : ℝ} (hu : 0 ≤ u) : 0 ≤ weight k s.re u := by unfold weight; positivity
  have hF : IntegrableOn F (Ioi 0) :=
    (coeff_integral k hs).1.norm.congr (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
      exact norm_integrand k s (le_of_lt hu))
  have hpoint {u : ℝ} (hu : 0 ≤ u) : f u ≤ F u :=
    mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (hw0 hu)
  have hf : IntegrableOn f (Ioi 0) := by
    apply hF.mono' hfC.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (hw0 (le_of_lt hu)))]
    exact hpoint (le_of_lt hu)
  have hsub : Icc a z ⊆ Ioi (0 : ℝ) := fun _ hu => ha.trans_le hu.1
  have hout := setIntegral_mono_on (s := Ioi (0 : ℝ) \ Icc a z)
    (hf.mono_set sdiff_subset) (hF.mono_set sdiff_subset)
    (measurableSet_Ioi.diff measurableSet_Icc) (fun u hu => hpoint (le_of_lt hu.1))
  have hin : (∫ u in Icc a z, f u) ≤
      (s.re-1/2)⁻¹^k * ∫ u in Icc a z, j u := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hf.mono_set hsub) ((hjC.integrableOn_Icc).const_mul _) measurableSet_Icc
    intro u hu
    calc
      _ ≤ max (g u) 0 * ((s.re-1/2)⁻¹^k * Real.exp (-(u/2))) :=
        mul_le_mul_of_nonneg_left (weight_le k hs (ha.le.trans hu.1)) (le_max_right _ _)
      _ = _ := by dsimp [j]; ring
  have hsplit := setIntegral_sdiff measurableSet_Icc hf hsub
  have htot := positive_moment k hs
  rw [show (fun u => 2 * max (U (Real.exp u)) 0 * weight k s.re u) =
    fun u => 2 * f u by ext u; dsimp [f, g]; ring, integral_const_mul] at htot
  change _ ≤ 2 * (_ * (∫ u in Icc a z, j u) + ∫ u in Ioi 0 \ Icc a z, F u)
  linarith


private lemma log_window_mass {a z : ℝ} (haz : a ≤ z) (ha : 2 ≤ Real.exp a) :
    (∫ u in Icc a z, max (U (Real.exp u)) 0 * Real.exp (-(u/2))) =
    ∫ x in Real.exp a..Real.exp z, max (-Q x) 0 / Real.sqrt x := by
  let H (x : ℝ) := max (U x) 0 / x / Real.sqrt x
  have hHC : ContinuousOn H (Real.exp '' uIcc a z) := by
    rintro x ⟨u, _, rfl⟩
    have h : ContinuousAt (fun x => max (U x) 0) (Real.exp u) :=
      (U_continuousAt_pos (Real.exp_pos u)).max continuousAt_const
    exact ((h.div continuousAt_id (Real.exp_pos _).ne').div
      Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr (Real.exp_pos _)).ne').continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv' (g := H)
    (fun u (_ : u ∈ uIcc a z) => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hHC
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haz]
  calc
    _ = ∫ u in a..z, (H ∘ Real.exp) u * Real.exp u := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [H, Function.comp_apply]
      rw [Real.exp_neg, Real.exp_half]
      field_simp [(Real.exp_pos u).ne', (Real.sqrt_pos.mpr (Real.exp_pos _)).ne']
    _ = _ := hsubst.trans (by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx2 := ha.trans ((uIcc_of_le (Real.exp_le_exp.mpr haz)) ▸ hx).1
      have hx0 : 0 < x := by linarith
      have ht := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
        D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hx2
      change Q x = _ at ht
      have heq : -Q x = U x / x := by
        rw [ht]; dsimp only [U]; field_simp [hx0.ne']; ring
      dsimp only [H]
      rw [heq, ← max_div_div_right hx0.le (U x) 0, zero_div])


private lemma coeff_completed (k : ℕ) {p : ℂ} (hp : 1 < p.re) :
    coeff k p = ((-1 : ℂ)^k / k.factorial) *
      iteratedDeriv k CompleteMangoldtAtOne.completed p := by
  unfold coeff
  apply congrArg (((-1 : ℂ)^k / k.factorial) * ·)
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp]
    with z (hz : 1 < z.re)
  exact (CompleteMangoldtAtOne.completed_disk_cauchy.1.1 z
    (by intro he; rw [he] at hz; norm_num at hz)).symm

private lemma disk_lower {p ρ : ℂ} {r : ℝ} (hp : 1 < p.re) (hρ : riemannZeta ρ = 0)
    (hd : 0 < ‖p-ρ‖) (hdr : ‖p-ρ‖ < r)
    (hcomplex : ∀ w ∈ Metric.closedBall p r, w ≠ 0 ∧ (riemannZeta w = 0 → w = ρ))
    (hreal : ∀ w ∈ Metric.closedBall (p.re : ℂ) r, w ≠ 0 ∧ riemannZeta w ≠ 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ k : ℕ in atTop,
      L ≤ ‖p-ρ‖^k * (‖coeff k p‖ + (coeff k (p.re : ℂ)).re) := by
  let F := CompleteMangoldtAtOne.completed
  let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ*(1-ρ))
  have hr := hd.trans hdr
  have hpρ := sub_ne_zero.mp (norm_pos_iff.mp hd)
  obtain ⟨_, hc, _⟩ := CompleteMangoldtLaurent.transform_integral_and_zero_germs.2 ρ hρ
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hJ := (CompleteMangoldtAtOne.completed_disk_cauchy.2 p ρ r hr hpρ hρ hcomplex).choose_spec
  have hconv := (hJ.2.2.2 hdr).2
  have hA : AnalyticOnNhd ℂ F (Metric.closedBall (p.re : ℂ) r) := fun w hw =>
    CompleteMangoldtAtOne.completed_disk_cauchy.1.2.2.1 w (hreal w hw).1 (hreal w hw).2
  obtain ⟨B, hB⟩ := (isCompact_closedBall (p.re : ℂ) r).exists_bound_of_continuousOn hA.continuousOn
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hr.le)
    ((div_lt_one hr).mpr hdr)).const_mul B
  have herr : ∀ᶠ k : ℕ in atTop, B * (‖p-ρ‖/r)^k < ‖c‖ / (4*‖p-ρ‖) := by
    apply (tendsto_order.mp (by simpa using hsmall :
      Tendsto (fun k : ℕ => B * (‖p-ρ‖/r)^k) atTop (𝓝 0))).2
    positivity
  refine ⟨‖c‖ / (4*‖p-ρ‖), by positivity, ?_⟩
  filter_upwards [herr, hconv] with k he hk
  have hcr := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
    (hA.differentiableOn.diffContOnCl_ball (Subset.rfl))
    (fun w hw => hB w (Metric.sphere_subset_closedBall hw))
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hrc : ‖coeff k (p.re : ℂ)‖ ≤ B / r^k := by
    rw [coeff_completed k (by simpa : 1 < (p.re : ℂ).re)]
    simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
    change 1 / (k.factorial : ℝ) * _ ≤ _
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfac]
    exact hcr.trans_eq (by ring)
  have hscale : ‖p-ρ‖^k * ‖coeff k (p.re : ℂ)‖ ≤ B * (‖p-ρ‖/r)^k :=
    (mul_le_mul_of_nonneg_left hrc (pow_nonneg hd.le _)).trans_eq (by rw [div_pow]; ring)
  have hcplx : ‖c‖ / 2 ≤ ‖p-ρ‖^(k+1) * ‖coeff k p‖ := by
    rw [coeff_completed k hp, ← norm_pow, ← norm_mul]
    simpa only [mul_assoc] using hk
  have hpos : ‖c‖ / (2*‖p-ρ‖) ≤ ‖p-ρ‖^k * ‖coeff k p‖ := by
    rw [div_mul_eq_div_div, div_le_iff₀ hd]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcplx
  have hneg := (abs_le.mp (Complex.abs_re_le_norm (coeff k (p.re : ℂ)))).1
  have hn := mul_le_mul_of_nonneg_left hneg (pow_nonneg hd.le k)
  rw [mul_neg] at hn
  rw [mul_add]
  have hid : ‖c‖ / (2*‖p-ρ‖) = 2 * (‖c‖ / (4*‖p-ρ‖)) := by ring
  linarith


private lemma compare_prime_mass {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, max (-Q t) 0 / Real.sqrt t) ≤
      ∫ t in x..y, max (-PrimeOnlyTailCorrection.primeTail t) 0 / Real.sqrt t := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hc := (PrimeOnlyTailCorrection.prime_power_window_correction.2 C (fun t _ => hC t)).1
  let H (t : ℝ) := (Chebyshev.theta t - t) / t^2
  have hmeas : Measurable H := (Chebyshev.theta_mono.measurable.sub measurable_id).div
    (measurable_id.pow_const 2)
  have hprod : StronglyMeasurable (fun p : ℝ × ℝ =>
      {p : ℝ × ℝ | p.1 < p.2}.indicator (fun t : ℝ × ℝ => H t.2) p) :=
    ((hmeas.comp measurable_snd).indicator (measurableSet_lt measurable_fst measurable_snd)).stronglyMeasurable
  have hm : Measurable PrimeOnlyTailCorrection.primeTail := by
    convert (hprod.integral_prod_right' (ν := volume)).measurable using 1
    ext t
    simp only [PrimeOnlyTailCorrection.primeTail, ← integral_indicator measurableSet_Ioi]
    rfl
  have hinterval : ∀ t ∈ uIcc x y, 1 ≤ t := fun t ht =>
    hx.trans ((uIcc_of_le hxy) ▸ ht).1
  have hq : ContinuousOn Q (uIcc x y) :=
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi.mono hinterval
  have hp t (ht : t ∈ uIcc x y) : 0 < t := zero_lt_one.trans_le (hinterval t ht)
  have hQ : IntervalIntegrable (fun t => max (-Q t) 0 / Real.sqrt t) volume x y :=
    ((hq.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne').intervalIntegrable
  have hmajor : IntervalIntegrable (fun t => (|Q t| + 2*C/Real.sqrt t) / Real.sqrt t) volume x y :=
    ((hq.abs.add (continuousOn_const.div Real.continuous_sqrt.continuousOn
      fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne')).div Real.continuous_sqrt.continuousOn
      fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne').intervalIntegrable
  have ht : IntegrableOn (fun t => max (-PrimeOnlyTailCorrection.primeTail t) 0 / Real.sqrt t)
      (Ioc x y) := by
    refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mp hmajor).mono'
      (((hm.neg.max measurable_const).div Real.continuous_sqrt.measurable).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    have ht1 := hx.trans ht.1.le
    have hsp := Real.sqrt_nonneg t
    rcases hc t ht1 with ⟨hlo, hhi⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (le_max_right _ _) hsp)]
    apply div_le_div_of_nonneg_right _ hsp
    exact max_le (by linarith [neg_le_abs (Q t)]) (by linarith [abs_nonneg (Q t)])
  apply intervalIntegral.integral_mono_on hxy hQ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr ht)
  intro t ht
  have h := (hc t (hx.trans ht.1)).1
  exact div_le_div_of_nonneg_right (max_le_max (by linarith) le_rfl) (Real.sqrt_nonneg t)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
