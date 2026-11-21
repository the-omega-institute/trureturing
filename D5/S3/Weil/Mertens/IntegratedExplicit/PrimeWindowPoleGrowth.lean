/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A right-half-strip zero forces positive Mangoldt mass on every sufficiently late power window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)

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

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
