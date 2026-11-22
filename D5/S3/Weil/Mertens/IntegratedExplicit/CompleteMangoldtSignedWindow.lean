/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtSignedWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtSignedWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired Mangoldt derivatives bound the weighted remainder of either sign. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtMoments

/-! Paired real and complex moments isolate the mass of a given sign on a log window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow

private def weight (k : ℕ) (σ u : ℝ) : ℝ :=
  u ^ k * Real.exp (-σ * u) / k.factorial

private def remainder (u : ℝ) : ℝ := U (Real.exp u)

private def normalizedDerivative (k : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k CompleteMangoldtAtOne.completed s

private def complexMoment (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  ((u : ℂ) ^ k / k.factorial) * (Complex.exp (-s * u) * (remainder u : ℂ))

private lemma normalizedDerivative_integral (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (complexMoment k s) (Ioi 0) ∧
      normalizedDerivative k s = ∫ u in Ioi 0, complexMoment k s u := by
  have hm := CompleteMangoldtMoments.iterated_derivative_moment k hs
  have heq : iteratedDeriv k CompleteMangoldtAtOne.completed s =
      iteratedDeriv k CompleteMangoldtLaurent.transform s := by
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    refine (CompleteMangoldtAtOne.completed_disk_cauchy.1.1 z) ?_
    intro he
    subst z
    norm_num at hz
  have hkernel :
      (fun u : ℝ => ((-1 : ℂ) ^ k / k.factorial) *
        ((-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (U (Real.exp u) : ℂ)))) =
        complexMoment k s := by
    funext u
    have hpow : (-1 : ℂ) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
      rw [← mul_pow, neg_one_mul, neg_neg]
    unfold complexMoment remainder
    calc
      _ = (((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) / k.factorial) *
          (Complex.exp (-s * u) * (U (Real.exp u) : ℂ)) := by ring
      _ = _ := by rw [hpow]
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, hkernel] using hm.1.const_mul ((-1 : ℂ) ^ k / k.factorial)
  · rw [normalizedDerivative, heq, hm.2, ← integral_const_mul, hkernel]

private lemma norm_complexMoment (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖complexMoment k s u‖ = |remainder u| * weight k s.re u := by
  simp [complexMoment, weight, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]
  ring

private lemma complexMoment_real (k : ℕ) (σ u : ℝ) :
    complexMoment k (σ : ℂ) u = ((remainder u * weight k σ u : ℝ) : ℂ) := by
  simp [complexMoment, weight, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div]
  ring

private lemma weight_nonneg (k : ℕ) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ weight k σ u := by unfold weight; positivity

private lemma weight_bound (k : ℕ) {σ α : ℝ} (hα : α < σ) {u : ℝ} (hu : 0 ≤ u) :
    weight k σ u ≤ (σ - α)⁻¹ ^ k * Real.exp (-α * u) := by
  let d := σ - α
  have hd : 0 < d := sub_pos.mpr hα
  have hp := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) k
  rw [mul_pow] at hp
  unfold weight
  calc
    _ = (d ^ k * u ^ k / k.factorial) * (d⁻¹ ^ k * Real.exp (-σ * u)) := by
      rw [div_mul_eq_mul_div, mul_assoc (d ^ k), mul_left_comm (u ^ k),
        ← mul_assoc (d ^ k), ← mul_pow, mul_inv_cancel₀ hd.ne', one_pow, one_mul]
    _ ≤ Real.exp (d * u) * (d⁻¹ ^ k * Real.exp (-σ * u)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add, show d * u + -σ * u = -α * u by dsimp [d]; ring]

/-- A paired moment bounds the prescribed sign of the remainder inside a log
window, with the absolute moment as the allowance outside the window. -/
theorem signed_window_moment_bound (k : ℕ) {p : ℂ} (hp : 1 < p.re)
    {a b α e : ℝ} (ha : 0 < a) (hab : a ≤ b) (hα : α < p.re)
    (he : e = 1 ∨ e = -1) :
    let D := fun s : ℂ =>
      ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k CompleteMangoldtAtOne.completed s
    let g := fun u : ℝ => U (Real.exp u)
    ‖D p‖ + e * (D (p.re : ℂ)).re ≤
      2 * (p.re - α)⁻¹ ^ k * (∫ u in a..b, max (e * g u) 0 * Real.exp (-α * u)) +
      2 * ∫ u in Ioi (0 : ℝ) \ Icc a b,
        |g u| * (u ^ k * Real.exp (-p.re * u) / k.factorial) := by
  let σ := p.re
  let A := Ioi (0 : ℝ)
  let W := Icc a b
  let K := weight k σ
  let g := remainder
  let f := fun u => max (e * g u) 0 * K u
  let F := fun u => |g u| * K u
  let G := fun u => max (e * g u) 0 * Real.exp (-α * u)
  have hWA : W ⊆ A := fun _ hu => ha.trans_le hu.1
  have hpMoment := normalizedDerivative_integral k hp
  have hrealMoment := normalizedDerivative_integral k (s := (σ : ℂ)) hp
  have hF : IntegrableOn F A := by
    apply (integrable_congr _).mp hpMoment.1.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_complexMoment k p hu.le
  have hSigned : IntegrableOn (fun u => g u * K u) A := by
    have h := hrealMoment.1.re
    change IntegrableOn (fun u => (complexMoment k (σ : ℂ) u).re) A at h
    simpa only [complexMoment_real, Complex.ofReal_re, g, K] using h
  have hePoint (u : ℝ) : |g u| * K u + e * (g u * K u) = 2 * f u := by
    have h : |g u| + e * g u = 2 * max (e * g u) 0 := by
      rcases he with rfl | rfl
      · by_cases h : 0 ≤ g u
        · simp [abs_of_nonneg h, max_eq_left h]; ring
        · have hn := le_of_not_ge h
          simp [abs_of_nonpos hn, max_eq_right hn]
      · by_cases h : 0 ≤ g u
        · simp [abs_of_nonneg h, max_eq_right (neg_nonpos.mpr h)]
        · have hn := le_of_not_ge h
          simp [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]; ring
    dsimp only [f]
    calc
      _ = (|g u| + e * g u) * K u := by ring
      _ = _ := by rw [h]; ring
  have hf : IntegrableOn f A := by
    have hf' := (hF.add (hSigned.const_mul e)).const_mul (1 / 2 : ℝ)
    refine hf'.congr (ae_of_all _ fun u => ?_)
    symm
    change f u = (1 / 2) * (|g u| * K u + e * (g u * K u))
    rw [hePoint]
    ring
  have hnorm : ‖normalizedDerivative k p‖ ≤ ∫ u in A, F u := by
    rw [hpMoment.2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_complexMoment k p hu.le
  have hre : (normalizedDerivative k (σ : ℂ)).re = ∫ u in A, g u * K u := by
    rw [hrealMoment.2]
    simp only [complexMoment_real, integral_complex_ofReal, Complex.ofReal_re, A, g, K]
  have hpair : ‖normalizedDerivative k p‖ + e * (normalizedDerivative k (σ : ℂ)).re ≤
      2 * ∫ u in A, f u := by
    rw [hre, ← integral_const_mul e]
    refine (add_le_add_left hnorm _).trans_eq ?_
    rw [← integral_add hF (hSigned.const_mul e), ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hePoint)
  have hsplit : (∫ u in A, f u) = (∫ u in W, f u) + ∫ u in A \ W, f u := by
    rw [setIntegral_sdiff measurableSet_Icc hf hWA]
    ring
  have hG : IntegrableOn G W := by
    have hcont : Continuous G :=
      ((U_exp_continuous.const_mul e).max continuous_const).mul (by fun_prop)
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hwindow : (∫ u in W, f u) ≤ (σ - α)⁻¹ ^ k * ∫ u in a..b, G u := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_mono_on (hf.mono_set hWA) (hG.const_mul _) measurableSet_Icc ?_
    intro u hu
    have hu0 : 0 ≤ u := (show 0 < u from hWA hu).le
    change max (e * g u) 0 * K u ≤ (σ - α)⁻¹ ^ k * (max (e * g u) 0 * Real.exp (-α * u))
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (weight_bound k hα hu0) (le_max_right _ _)
  have htail : (∫ u in A \ W, f u) ≤ ∫ u in A \ W, F u := by
    refine setIntegral_mono_on (hf.mono_set sdiff_subset) (hF.mono_set sdiff_subset)
      (measurableSet_Ioi.diff measurableSet_Icc) ?_
    intro u hu
    have hmajor : max (e * g u) 0 ≤ |g u| := by
      apply max_le _ (abs_nonneg _)
      rcases he with rfl | rfl
      · simpa using le_abs_self (g u)
      · simpa using neg_le_abs (g u)
    exact mul_le_mul_of_nonneg_right hmajor (weight_nonneg k σ hu.1.le)
  change ‖normalizedDerivative k p‖ + e * (normalizedDerivative k (σ : ℂ)).re ≤
    2 * (σ - α)⁻¹ ^ k * (∫ u in a..b, G u) + 2 * ∫ u in A \ W, F u
  rw [hsplit, mul_add] at hpair
  exact hpair.trans (by linarith only [hwindow, htail])

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow
