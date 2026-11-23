/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Prime-only window mass from actual Robin-weighted negative mass. -/

import D5.S3.Weil.Mertens.WeightedTailWindowMass
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual Chebyshev tail on an inner power window gives a Robin criterion
using the negative endpoint defect of the outer window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass

open Filter MeasureTheory Real Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.WeightedTailWindowMass
  (endpointDefect massFactor weightedNegativeMass negative_mass_le weightedNegativeMass_nonneg)
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction (golden_right_half_strip_implies_rh)
open PrimeOnlyTailCorrection (primeTail)

/-- The actual prime-only mass on the test window. The prime-power correction
is integrated over that window and the weighted negative mass extends to B. -/
theorem prime_mass_le {C Y X B : ℝ} (hY : 2 ≤ Y) (hYX : Y ≤ X) (hXB : X ≤ B)
    (hC : ∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * sqrt t) :
    (∫ x in Y..X, max (-primeTail x) 0 / sqrt x) ≤
      massFactor Y * weightedNegativeMass psiErrorKernel Y B +
        2 * (sqrt X - sqrt Y) * max (-endpointDefect psiErrorKernel B) 0 +
        2 * C * log (X / Y) := by
  have hY1 : 1 ≤ Y := by linarith
  have hk : IntegrableOn psiErrorKernel (Ioi Y) :=
    chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi hY1)
  have hQ : (∫ x in Y..X, max (-Q x) 0 / sqrt x) ≤
      massFactor Y * weightedNegativeMass psiErrorKernel Y B +
        2 * (sqrt X - sqrt Y) * max (-endpointDefect psiErrorKernel B) 0 :=
    negative_mass_le hY hYX hXB hk
  exact (PrimeWindowPoleGrowth.compare_prime_mass hC hY1 hYX).2.trans
    (add_le_add hQ le_rfl)

/-- The outer-window negative mass and the endpoint payment at the scale √Y. -/
def robinBudget (Y b : ℝ) : ℝ :=
  weightedNegativeMass psiErrorKernel Y (Y ^ b) +
    sqrt Y * max (-endpointDefect psiErrorKernel (Y ^ b)) 0

private lemma two_le_exp_one : (2 : ℝ) ≤ exp 1 := by
  simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)

/-- Testing the inner power window costs a factor Y^((d-1)/2) on the
outer-window budget, with a logarithmic prime-power correction. -/
theorem prime_mass_le_power {C Y d b : ℝ} (hY : exp 1 ≤ Y) (hd : 1 ≤ d) (hdb : d ≤ b)
    (hC : ∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * sqrt t) :
    (∫ x in Y..Y ^ d, max (-primeTail x) 0 / sqrt x) ≤
      4 * Y ^ ((d - 1) / 2) * robinBudget Y b + 2 * C * (d - 1) * log Y := by
  have hY2 := two_le_exp_one.trans hY
  have hY1 : 1 < Y := by linarith
  have hY0 := zero_lt_one.trans hY1
  have hYX : Y ≤ Y ^ d := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hY1.le hd
  have hXB := rpow_le_rpow_of_exponent_le hY1.le hdb
  have hlog : 1 ≤ log Y := by
    simpa only [log_exp] using log_le_log (exp_pos 1) hY
  have hfactor : massFactor Y ≤ 4 := by
    have hden : 0 < log Y * (1 + log Y) := by positivity
    have hratio : (log Y + 2) / (log Y * (1 + log Y)) ≤ 3 / 2 :=
      (div_le_iff₀ hden).2 (by nlinarith only [hlog, sq_nonneg (log Y - 1)])
    unfold massFactor
    linarith only [hratio]
  let M := weightedNegativeMass psiErrorKernel Y (Y ^ b)
  let D := max (-endpointDefect psiErrorKernel (Y ^ b)) 0
  let q : ℝ := (d - 1) / 2
  have hM : 0 ≤ M := weightedNegativeMass_nonneg (k := psiErrorKernel) hY1 (hYX.trans hXB)
  have hD : 0 ≤ D := le_max_right _ _
  have hpow : 1 ≤ Y ^ q := by
    have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hd) (by norm_num)
    simpa only [rpow_zero] using rpow_le_rpow_of_exponent_le hY1.le hq
  have hsqrt : sqrt (Y ^ d) = Y ^ q * sqrt Y := by
    rw [sqrt_eq_rpow (Y ^ d), ← rpow_mul hY0.le, sqrt_eq_rpow Y, ← rpow_add hY0]
    rw [show d * (1 / 2 : ℝ) = q + 1 / 2 by dsimp [q]; ring]
  have hlogcost : log (Y ^ d / Y) = (d - 1) * log Y := by
    rw [log_div (rpow_pos_of_pos hY0 _).ne' hY0.ne', log_rpow hY0]
    ring
  have hupper := prime_mass_le hY2 hYX hXB hC
  rw [hlogcost] at hupper
  have hm : massFactor Y * M ≤ 4 * M := mul_le_mul_of_nonneg_right hfactor hM
  have he : 2 * (sqrt (Y ^ d) - sqrt Y) * D ≤ 2 * sqrt (Y ^ d) * D :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self _ (sqrt_nonneg Y)) (by norm_num)) hD
  change _ ≤ 4 * Y ^ q * (M + sqrt Y * D) + 2 * C * (d - 1) * log Y
  calc
    _ ≤ massFactor Y * M + 2 * (sqrt (Y ^ d) - sqrt Y) * D +
          2 * C * (d - 1) * log Y := by
      simpa only [mul_assoc] using hupper
    _ ≤ 4 * M + 2 * sqrt (Y ^ d) * D + 2 * C * (d - 1) * log Y :=
      add_le_add (add_le_add hm he) le_rfl
    _ = 4 * M + (2 * Y ^ q) * (sqrt Y * D) + 2 * C * (d - 1) * log Y := by
      rw [hsqrt]
      ring
    _ ≤ (4 * Y ^ q) * M + (4 * Y ^ q) * (sqrt Y * D) + 2 * C * (d - 1) * log Y := by
      refine add_le_add (add_le_add ?_ ?_) le_rfl
      · exact mul_le_mul_of_nonneg_right (by linarith only [hpow]) hM
      · exact mul_le_mul_of_nonneg_right (by linarith only [hpow]) (mul_nonneg (sqrt_nonneg Y) hD)
    _ = _ := by ring

/-- A zero in the open right half-strip forces the rescaled Robin budget to
grow on every sufficiently late outer power window. After b, the zero, and ε
are fixed, the proof chooses a single inner exponent d with 1 < d < b. -/
theorem off_line_zero_forces_robin_budget {z : ℂ} (hz : riemannZeta z = 0)
    (hβ : 1 / 2 < z.re) (hβ₁ : z.re < 1) {b ε : ℝ} (hb : 1 < b) (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in atTop, Y ^ (z.re - 1 / 2 - ε) ≤ robinBudget Y b := by
  let σ : ℝ := z.re - 1 / 2
  have hσ : 0 < σ := sub_pos.mpr hβ
  have hroom : 0 < 1 - z.re := sub_pos.mpr hβ₁
  have hden : 0 < 4 * (1 - z.re) := mul_pos (by norm_num) hroom
  obtain ⟨d, hd, hd'⟩ := exists_between
    (lt_min hb (lt_add_of_pos_right 1 (div_pos hε hden)))
  have hdb : d < b := (lt_min_iff.mp hd').1
  have hdclose := (lt_min_iff.mp hd').2
  have hloss : (d - 1) * (4 * (1 - z.re)) < ε :=
    (lt_div_iff₀ hden).1 (by linarith only [hdclose])
  let δ : ℝ := min (ε / 4) (σ / 2)
  have hδ : 0 < δ := lt_min (by positivity) (half_pos hσ)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδσ : δ ≤ σ / 2 := min_le_right _ _
  let p : ℝ := d * σ - δ
  let q : ℝ := (d - 1) / 2
  let gap : ℝ := p - (q + (σ - ε))
  have hp : 0 < p := by
    dsimp only [p]
    nlinarith only [hδσ, hσ, mul_pos (sub_pos.mpr hd) hσ]
  have hgap : 0 < gap := by
    change 0 < d * (z.re - 1 / 2) - δ - ((d - 1) / 2 + (z.re - 1 / 2 - ε))
    nlinarith only [hloss, hδε, hε]
  have hlower := PrimeWindowPoleGrowth.off_line_zero_forces_window_mass hz hβ hd hδ
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlog : ∀ᶠ Y : ℝ in atTop, 2 * C * (d - 1) * log Y ≤ (1 / 2 : ℝ) * Y ^ p := by
    have h := ((isLittleO_log_rpow_atTop hp).const_mul_left (2 * C * (d - 1))).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with Y hY hY0
    have habs : |2 * C * (d - 1) * log Y| ≤ (1 / 2 : ℝ) * Y ^ p := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hY0 p)] using hY
    exact (le_abs_self _).trans habs
  have hlarge : ∀ᶠ Y : ℝ in atTop, (8 : ℝ) ≤ Y ^ gap :=
    (tendsto_rpow_atTop hgap).eventually_ge_atTop 8
  filter_upwards [eventually_ge_atTop (exp 1), hlower, hlog, hlarge] with Y hY hlow hlogY hlargeY
  have hY0 := (exp_pos 1).trans_le hY
  have hupper := prime_mass_le_power hY hd.le hdb.le (fun t _ => hC t)
  have hpaid : (1 / 2 : ℝ) * Y ^ p ≤ 4 * Y ^ q * robinBudget Y b := by
    have hlow' : Y ^ p ≤ ∫ x in Y..Y ^ d, max (-primeTail x) 0 / sqrt x := hlow
    have hupper' : (∫ x in Y..Y ^ d, max (-primeTail x) 0 / sqrt x) ≤
        4 * Y ^ q * robinBudget Y b + 2 * C * (d - 1) * log Y := hupper
    linarith only [hlow', hupper', hlogY]
  have hscale : 8 * (Y ^ q * Y ^ (σ - ε)) ≤ Y ^ p := by
    calc
      _ ≤ Y ^ gap * (Y ^ q * Y ^ (σ - ε)) := mul_le_mul_of_nonneg_right hlargeY
        (mul_nonneg (rpow_nonneg hY0.le _) (rpow_nonneg hY0.le _))
      _ = _ := by
        rw [← rpow_add hY0 q (σ - ε), ← rpow_add hY0 gap (q + (σ - ε)),
          show gap + (q + (σ - ε)) = p by dsimp only [gap]; ring]
  have hscaled : (4 * Y ^ q) * Y ^ (σ - ε) ≤ (4 * Y ^ q) * robinBudget Y b := by
    calc
      _ = (1 / 2 : ℝ) * (8 * (Y ^ q * Y ^ (σ - ε))) := by ring
      _ ≤ (1 / 2 : ℝ) * Y ^ p := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ _ := hpaid
  exact (mul_le_mul_iff_right₀ (mul_pos (by norm_num) (rpow_pos_of_pos hY0 q))).1 hscaled

/-- Joint subpower control of the Robin mass and √Y times the negative
outer endpoint defect on arbitrarily late windows implies RH. -/
theorem rh_of_frequently_small_robin_windows {b : ℝ} (hb : 1 < b)
    (hwindows : ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop, robinBudget Y b ≤ Y ^ η) :
    RiemannHypothesis := by
  apply golden_right_half_strip_implies_rh
  intro z hz hβ hβ₁
  let η : ℝ := (z.re - 1 / 2) / 3
  have hη : 0 < η := div_pos (sub_pos.mpr hβ) (by norm_num)
  have hlower := off_line_zero_forces_robin_budget hz hβ hβ₁ hb hη
  obtain ⟨Y, hgood, hlow, hY⟩ := ((hwindows η hη).and_eventually
    (hlower.and (eventually_gt_atTop (1 : ℝ)))).exists
  have hstrict : Y ^ η < Y ^ (z.re - 1 / 2 - η) :=
    rpow_lt_rpow_of_exponent_lt hY (by dsimp only [η]; linarith only [hβ])
  exact (not_lt_of_ge (hlow.trans hgood)) hstrict

#print axioms prime_mass_le
#print axioms prime_mass_le_power
#print axioms off_line_zero_forces_robin_budget
#print axioms rh_of_frequently_small_robin_windows

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
