/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A right-half-strip zero forces positive Mangoldt mass on every sufficiently late power window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import D5.S3.Analytic.Laplace.CriticalGammaWindow
import D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

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


private lemma compare_prime_mass {C x y : ℝ}
    (hC : ∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t)
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    let A := ∫ t in x..y, max (-Q t) 0 / Real.sqrt t
    let B := ∫ t in x..y, max (-PrimeOnlyTailCorrection.primeTail t) 0 / Real.sqrt t
    A ≤ B ∧ B ≤ A + 2*C*Real.log (y/x) := by
  dsimp only
  have hc := (PrimeOnlyTailCorrection.prime_power_window_correction.2 C hC).1
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
  have hbudget := (PrimeOnlyTailCorrection.prime_power_window_correction.2 C hC).2 x y hx hxy
  dsimp only at hbudget
  simp only [sub_div] at hbudget
  rw [intervalIntegral.integral_sub ((intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr ht)
    hQ] at hbudget
  constructor <;> linarith [hbudget.1, hbudget.2]


private lemma input_growth : ∃ M : ℝ, 0 ≤ M ∧
    ∀ u, 0 ≤ u → |U (Real.exp u)| ≤ M * Real.exp (2*u) := by
  let K := Real.log 4 + 4
  let c := 1 + Real.eulerMascheroniConstant
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨2*K+1+|c|, by positivity, ?_⟩
  intro u hu
  let x := Real.exp u
  have hx : 1 ≤ x := Real.one_le_exp hu
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  let S := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hψ := Chebyshev.psi_nonneg x
  have hSX : S ≤ Chebyshev.psi x := by
    unfold S Chebyshev.psi
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    exact div_le_self ArithmeticFunction.vonMangoldt_nonneg (by exact_mod_cast hn1)
  have hψb : Chebyshev.psi x ≤ K*x := Chebyshev.psi_le_const_mul_self hx0
  have hx2 : x ≤ x^2 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hA : x*S ≤ K*x^2 :=
    (mul_le_mul_of_nonneg_left (hSX.trans hψb) hx0).trans_eq (by ring)
  have hB := hψb.trans (mul_le_mul_of_nonneg_left hx2 hK)
  have hl : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx)).trans
    (by linarith)
  have hC : x*Real.log x ≤ x^2 := (mul_le_mul_of_nonneg_left hl hx0).trans_eq (by ring)
  have hC0 := mul_nonneg hx0 (Real.log_nonneg hx)
  have hD := (mul_le_mul_of_nonneg_right (le_abs_self c) hx0).trans
    (mul_le_mul_of_nonneg_left hx2 (abs_nonneg c))
  have hD' := (mul_le_mul_of_nonneg_right (neg_le_abs c) hx0).trans
    (mul_le_mul_of_nonneg_left hx2 (abs_nonneg c))
  rw [show Real.exp (2*u) = x^2 by rw [two_mul, Real.exp_add]; dsimp [x]; ring, abs_le]
  change -( _ * x^2) ≤ x*S - Chebyshev.psi x - x*Real.log x + c*x ∧ _
  dsimp only [U]
  change _ ∧ x*S - Chebyshev.psi x - x*Real.log x + c*x ≤ _ * x^2
  constructor <;> nlinarith [mul_nonneg hx0 hS, mul_nonneg (abs_nonneg c) (sq_nonneg x),
    mul_nonneg hK (sq_nonneg x)]


private lemma select_parameters {v b ε : ℝ} (hv : 0 < v) (hb : 1 < b) (hε : 0 < ε) :
    ∃ h δ : ℝ, 1 < h ∧ h < b ∧ 0 < δ ∧ δ < v ∧ b*v-ε < h*(v-δ) := by
  have H : max 1 ((b*v-ε/2)/v) < b :=
    max_lt hb ((div_lt_iff₀ hv).mpr (by linarith))
  obtain ⟨h, hh, hhb⟩ := exists_between H
  obtain ⟨hh1, hh2⟩ := max_lt_iff.mp hh
  have hh0 : 0 < h := zero_lt_one.trans hh1
  obtain ⟨δ, hδ, hδ'⟩ := exists_between (lt_min hv (div_pos (half_pos hε) hh0))
  obtain ⟨hδv, hs⟩ := lt_min_iff.mp hδ'
  have hi := (div_lt_iff₀ hv).mp hh2
  have hj := (lt_div_iff₀ hh0).mp hs
  exact ⟨h, δ, hh1, hhb, hδ, hδv, by nlinarith⟩

private lemma rate_gain {β δ σ d : ℝ} (hσ : 2 < σ) (hd : 0 < d)
    (hgap : 0 < β-1/2-δ) (hupper : d < σ-β+δ) :
    β-1/2-δ < σ * Real.log ((σ-1/2)/d) := by
  have hσ' : 0 < σ-1/2 := by linarith
  have qpos := div_pos hσ' hd
  have hlog := Real.one_sub_inv_le_log_of_pos qpos
  rw [inv_div] at hlog
  have hs : (β-1/2-δ) * (σ-1/2) < σ*((σ-1/2)-d) := by
    nlinarith [mul_pos (show 0 < σ by linarith) (sub_pos.mpr hupper)]
  have ht : β-1/2-δ < σ * (1 - d/(σ-1/2)) := by
    calc
      _ < (σ*((σ-1/2)-d))/(σ-1/2) := (lt_div_iff₀ hσ').mpr hs
      _ = _ := by rw [mul_div_assoc, sub_div, div_self hσ'.ne']
  exact ht.trans_le (mul_le_mul_of_nonneg_left hlog (by linarith))

private lemma exp_le_floor_power {q T τ C : ℝ} (hq : 1 < q) (hC : 0 < C)
    (hτ : τ < T * Real.log q) :
    ∀ᶠ a : ℝ in atTop, Real.exp (a*τ) ≤ C*q^⌊T*a⌋₊ := by
  have hq0 := zero_lt_one.trans hq
  have hlog := Real.log_pos hq
  have hgap := sub_pos.mpr hτ
  filter_upwards [eventually_ge_atTop ((Real.log q - Real.log C) / (T*Real.log q-τ))]
    with a ha
  have hA := (div_le_iff₀ hgap).mp ha
  have hK := mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one (T*a)).le hlog.le
  have hpow : q^⌊T*a⌋₊ = Real.exp ((⌊T*a⌋₊ : ℝ)*Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  rw [hpow, ← Real.exp_log hC]
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith


private lemma absorb_tails {d σ L C : ℝ} (hd : 0 < d) (hσ : 1 < σ)
    (hdσ : d < σ) (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, ∀ A : ℝ,
      L ≤ d^k * (2 * ((σ-1/2)⁻¹^k * A + C * σ⁻¹^k)) →
      (L/4) * ((σ-1/2)/d)^k ≤ A := by
  have hσ0 := zero_lt_one.trans hσ
  have hσ' : 0 < σ-1/2 := by linarith
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hσ0.le)
    ((div_lt_one hσ0).mpr hdσ)).const_mul (2*C)
  have he : ∀ᶠ k : ℕ in atTop, 2*C*(d/σ)^k < L/2 := by
    apply (tendsto_order.mp (by simpa using hsmall :
      Tendsto (fun k : ℕ => 2*C*(d/σ)^k) atTop (𝓝 0))).2 _ (half_pos hL)
  filter_upwards [he] with k hk A hA
  have hrew : d^k * (2 * ((σ-1/2)⁻¹^k * A + C * σ⁻¹^k)) =
      2*((d/(σ-1/2))^k*A) + 2*C*(d/σ)^k := by
    rw [div_pow, div_pow, inv_pow, inv_pow]; ring
  rw [hrew] at hA
  have hm : L/4 ≤ (d/(σ-1/2))^k*A := by linarith
  calc
    _ = (L/4)/(d/(σ-1/2))^k := by
      rw [div_eq_mul_inv _ ((d/(σ-1/2))^k), ← inv_pow, inv_div]
    _ ≤ _ := (div_le_iff₀ (pow_pos (div_pos hd hσ') k)).mpr (by simpa [mul_comm] using hm)

open PrimeOnlyTailCorrection (primeTail)

/-- A zero with real part above one half forces prime-only negative-part mass
on every sufficiently late power window, at the full exponent up to any
positive loss. -/
theorem off_line_zero_forces_window_mass {z₀ : ℂ} (hz : riemannZeta z₀ = 0)
    (hβ : 1/2 < z₀.re) {b ε : ℝ} (hb : 1 < b) (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in atTop, Y^(b*(z₀.re-1/2)-ε) ≤
      ∫ x in Y..Y^b, max (-primeTail x) 0 / Real.sqrt x := by
  obtain ⟨h, δ, hh, hhb, hδ, hδv, hg⟩ :=
    select_parameters (sub_pos.mpr hβ) hb hε
  have hgamma := D5.S3.Analytic.Laplace.CriticalGammaWindow.adjustable_window_off_mass hh hhb
  obtain ⟨σ, hσ2, hsign, hleft, hright⟩ :=
    ((eventually_gt_atTop (2 : ℝ)).and (hgamma.1 0)).exists
  have hσ : 1 < σ := by linarith
  have hσ0 : 0 < σ := by linarith
  have hh0 := zero_lt_one.trans hh
  have hb0 := zero_lt_one.trans hb
  obtain ⟨p, ρ, r, hpre, hρ, hd₀, hdr₀, hr, hre, hcomplex⟩ :=
    D5.S3.Weil.ZetaBridge.EqualRadiusZeroDisks.equal_radius_zero_disks hz hσ2 hδ hδv
  let d := ‖p-ρ‖
  have hd : 0 < d := by simpa [d, dist_eq_norm] using hd₀
  have hdr : d < r := by simpa [d, dist_eq_norm] using hdr₀
  have hhp : 1 < p.re := hpre ▸ hσ
  have hcoord (w : ℂ) (hw : 1/2 < w.re) : w ≠ 0 := by
    rintro rfl; norm_num at hw
  obtain ⟨L, hL, hD⟩ := disk_lower hhp hρ hd hdr
    (fun w hw => ⟨hcoord w (hcomplex w hw).1, (hcomplex w hw).2⟩)
    (fun w hw => by rw [hpre] at hw; exact ⟨hcoord w (hre w hw).1, (hre w hw).2⟩)
  obtain ⟨M, hM0, hM⟩ := input_growth
  let C := M * (1/σ + b/(h*σ))
  let q := (σ-1/2)/d
  have hd' : d < σ-z₀.re+δ := hdr.trans hr
  have hq : 1 < q := (one_lt_div hd).mpr (by linarith)
  have hrate := rate_gain hσ2 hd (by linarith : 0 < z₀.re-1/2-δ) hd'
  have hτ : b*(z₀.re-1/2)-ε < σ*h*Real.log q := by
    change _ < σ*h*Real.log ((σ-1/2)/d)
    nlinarith [mul_lt_mul_of_pos_left hrate hh0]
  have hexp := exp_le_floor_power hq (by positivity : 0 < L/4) hτ
  have hAbs := absorb_tails (C := C) hd hσ (by linarith : d < σ) hL
  have hK : Tendsto (fun a : ℝ => ⌊σ*h*a⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Filter.tendsto_id.const_mul_atTop (mul_pos hσ0 hh0))
  have hlogwin : ∀ᶠ a : ℝ in atTop, Real.exp (a*(b*(z₀.re-1/2)-ε)) ≤
      ∫ x in Real.exp a..Real.exp (b*a), max (-primeTail x) 0 / Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_exp_atTop (eventually_ge_atTop 2),
      hK.eventually hD, hK.eventually hAbs, hexp] with a ha h2 hdisc habs he
    let k := ⌊σ*h*a⌋₊
    have hab : a ≤ b*a := by nlinarith
    have Htail := (hgamma.2 hsign ha U_exp_continuous.measurable hM).2
    have hTail : (∫ u in Ioi (0 : ℝ) \ Icc a (b*a), |U (Real.exp u)| * weight k σ u)
        ≤ C * σ⁻¹^k := by
      apply Htail.trans
      have h1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hleft.le) ha.le)
      have h2' := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hright.le) ha.le)
      calc
        _ ≤ (M*σ⁻¹^k) * (1/σ + b/(h*σ)*1) := by gcongr
        _ = _ := by dsimp [C]; ring
    have hB := coeff_window k hhp (a := a) (z := b*a) ha
    rw [hpre, log_window_mass hab h2] at hB
    obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    have hmass := (compare_prime_mass (C := C₀) (fun t _ => hC₀ t) (Real.one_le_exp ha.le)
      (Real.exp_le_exp.mpr hab)).1
    apply he.trans
    apply habs
    have hdisc' : L ≤ d^k*(‖coeff k p‖ + (coeff k (σ : ℂ)).re) := by simpa only [hpre] using hdisc
    apply hdisc'.trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hd.le k)
    exact hB.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hmass (pow_nonneg (inv_nonneg.mpr (by linarith)) k)) hTail)
      (by norm_num))
  filter_upwards [Real.tendsto_log_atTop.eventually hlogwin, eventually_gt_atTop (0 : ℝ)]
    with Y hY hy
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hy]
  simpa only [Real.exp_log hy, mul_comm b (Real.log Y)] using hY


private lemma eventual_small_windows (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 < b)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, (∫ x in Y..Y^b, max (-primeTail x) 0 / Real.sqrt x) ≤ Y^η := by
  let ℓ := D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.firstLiMass + 1
  obtain ⟨u₀, hwhole⟩ := eventually_atTop.mp ((RHSharpActualEnvelope.actual_G_control hRH).1 1 one_pos)
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := (ℓ+2*C)*(b-1)
  have H : ∀ᶠ a : ℝ in atTop, (∫ x in Real.exp a..Real.exp (b*a),
      max (-primeTail x) 0 / Real.sqrt x) ≤ Real.exp (a*η) := by
    filter_upwards [eventually_ge_atTop u₀, eventually_gt_atTop (0 : ℝ),
      Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_ge_atTop (2*K/η^2)] with a hau ha ha2 hbig
    have hab : a ≤ b*a := by nlinarith
    have hG : (∫ u in Icc a (b*a), max (U (Real.exp u)) 0 * Real.exp (-(u/2))) ≤ ℓ*(b*a-a) := by
      have hc : Continuous (fun u => max (U (Real.exp u)) 0 * Real.exp (-(u/2))) :=
        (U_exp_continuous.max continuous_const).mul (by fun_prop)
      calc
        _ ≤ ∫ _ in Icc a (b*a), ℓ := by
          apply setIntegral_mono_on hc.integrableOn_Icc continuous_const.integrableOn_Icc measurableSet_Icc
          intro u hu
          have H := (hwhole u (hau.trans hu.1)).le
          change |Real.exp (-u/2) * U (Real.exp u)| ≤ ℓ at H
          rw [abs_mul, abs_of_pos (Real.exp_pos _)] at H
          rw [neg_div] at H
          exact (mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
            (Real.exp_pos _).le).trans (by simpa only [mul_comm] using H)
        _ = _ := by rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_const]; simp [mul_comm]
    rw [log_window_mass hab ha2] at hG
    have hc := (compare_prime_mass (C := C) (fun t _ => hC t) (Real.one_le_exp ha.le)
      (Real.exp_le_exp.mpr hab)).2
    rw [← Real.exp_sub, Real.log_exp] at hc
    have hp := Real.pow_div_factorial_le_exp (a*η) (mul_nonneg ha.le hη.le) 2
    norm_num at hp
    have hKA := (div_le_iff₀ (sq_pos_of_pos hη)).mp hbig
    calc
      _ ≤ K*a := hc.trans (by dsimp [K]; nlinarith [hG])
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hKA ha.le]
  filter_upwards [Real.tendsto_log_atTop.eventually H, eventually_gt_atTop (0 : ℝ)] with Y hY hy
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hy]
  simpa only [Real.exp_log hy, mul_comm b (Real.log Y)] using hY

/-- For each fixed power-window width above one, the Riemann hypothesis is
equivalent to arbitrarily late windows of subpower prime-only negative mass. -/
theorem rh_iff_frequently_small_prime_windows {b : ℝ} (hb : 1 < b) :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop,
      (∫ x in Y..Y^b, max (-primeTail x) 0 / Real.sqrt x) ≤ Y^η := by
  constructor
  · exact fun hRH _ hη => (eventual_small_windows hRH hb hη).frequently
  · intro h
    apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
    intro z hz hhalf _
    let η := b*(z.re-1/2)/3
    have hη : 0 < η := div_pos (mul_pos (zero_lt_one.trans hb) (sub_pos.mpr hhalf)) (by norm_num)
    have hlower := off_line_zero_forces_window_mass hz hhalf hb hη
    obtain ⟨Y, hY, hlow, hY1⟩ := ((h η hη).and_eventually (hlower.and
      (eventually_gt_atTop (1 : ℝ)))).exists
    have hstrict : Y^η < Y^(b*(z.re-1/2)-η) :=
      Real.rpow_lt_rpow_of_exponent_lt hY1 (by dsimp [η] at *; linarith)
    exact (not_lt_of_ge (hlow.trans hY)) hstrict

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
