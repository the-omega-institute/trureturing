/- GID: D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/RobinWindowSharpLower
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Sharp lower power bounds for actual weighted Robin window mass. -/

import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass

/-! The inner window contributes its square-root scale to the endpoint payment.
The comparison coefficient on the full weighted negative mass stays bounded. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi weighted_eq)
open D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope (actual_terminal_defect_exp_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.WeightedTailInverse (a)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens.WeightedTailWindowMass
  (endpointDefect massFactor weightedNegativeMass weightedNegativeMass_nonneg)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap
  (zeroAbscissa zero_real_parts_nonempty zero_re_le_abscissa)

namespace D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower

private lemma eventually_const_mul_rpow_le_rpow {u v : ℝ} (huv : u < v) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, C * Y ^ u ≤ Y ^ v := by
  have hlarge : ∀ᶠ Y : ℝ in atTop, C ≤ Y ^ (v - u) :=
    (tendsto_rpow_atTop (sub_pos.mpr huv)).eventually_ge_atTop C
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlarge] with Y hY hCY
  calc
    _ ≤ Y ^ (v - u) * Y ^ u := mul_le_mul_of_nonneg_right hCY (rpow_nonneg hY.le _)
    _ = _ := by rw [← rpow_add hY, sub_add_cancel]

/-- Under a fixed uniform zero strip, an actual zero to the right of the
critical line forces eventual growth of the full Robin weighted negative mass.
The target exponent lies below the pole exponent and the pole exponent exceeds
both the endpoint exponent and zero. -/
theorem off_line_zero_forces_weighted_negative_mass_of_actual_strip
    {alpha d b r : ℝ} {rho : ℂ} (ha : 0 < alpha) :
    let data := fun z : ℂ => (IsNontrivialZero z, weightedNegativeMass psiErrorKernel)
    (∀ z : ℂ, (data z).1 → z.re ≤ 1 - alpha) →
    1 < d → d < b → (data rho).1 → 1 / 2 < rho.re →
    max r (max (d / 2 - b * alpha) 0) < d * (rho.re - 1 / 2) →
    ∀ᶠ Y : ℝ in atTop, Y ^ r ≤ (data 0).2 Y (Y ^ b) := by
  intro data hstrip hd hdb hzero hβ hgap
  dsimp only [data] at hstrip hzero ⊢
  let p : ℝ := d / 2 - b * alpha
  obtain ⟨s, hbelow, hpole⟩ := exists_between hgap
  obtain ⟨hrs, hcorrections⟩ := max_lt_iff.mp hbelow
  have hps : p < s := (max_lt_iff.mp hcorrections).1
  have hs : 0 < s := (max_lt_iff.mp hcorrections).2
  have hζ : riemannZeta rho = 0 := hzero.1
  have hprime :=
    PrimeWindowPoleGrowth.off_line_zero_forces_window_mass hζ hβ hd (sub_pos.mpr hpole)
  rw [show d * (rho.re - 1 / 2) - (d * (rho.re - 1 / 2) - s) = s by ring] at hprime
  have hhalf : alpha ≤ 1 / 2 := by linarith only [hβ, hstrip rho hzero]
  obtain ⟨C, hC, hdefect⟩ := actual_terminal_defect_exp_bound ha hhalf hstrip
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hendGap := eventually_const_mul_rpow_le_rpow hps (8 * C)
  have hmassGap := eventually_const_mul_rpow_le_rpow hrs 8
  have hlogGap := ((isLittleO_log_rpow_atTop hs).const_mul_left (2 * K * (d - 1))).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [eventually_ge_atTop (exp 1), hprime, hendGap, hmassGap, hlogGap] with
    Y hY hprimeY hendGapY hmassGapY hlogGapY
  have hY0 : 0 < Y := (exp_pos 1).trans_le hY
  have hY1 : 1 < Y := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hY
  have hY2 : 2 ≤ Y := by
    have he : (2 : ℝ) ≤ exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
    exact he.trans hY
  have hYX : Y ≤ Y ^ d := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hY1.le hd.le
  have hXB : Y ^ d ≤ Y ^ b := rpow_le_rpow_of_exponent_le hY1.le hdb.le
  have hupper := RobinWindowMass.prime_mass_le hY2 hYX hXB (fun t _ => hK t)
  let M := weightedNegativeMass psiErrorKernel Y (Y ^ b)
  let D := max (-endpointDefect psiErrorKernel (Y ^ b)) 0
  have hM : 0 ≤ M := weightedNegativeMass_nonneg (k := psiErrorKernel) hY1 (hYX.trans hXB)
  have hD : 0 ≤ D := le_max_right _ _
  have hlog : 1 ≤ log Y := by
    simpa only [log_exp] using log_le_log (exp_pos 1) hY
  have hfactor : massFactor Y ≤ 4 := by
    have hden : 0 < log Y * (1 + log Y) := by positivity
    have hratio : (log Y + 2) / (log Y * (1 + log Y)) ≤ 3 / 2 :=
      (div_le_iff₀ hden).2 (by nlinarith only [hlog, sq_nonneg (log Y - 1)])
    unfold massFactor
    linarith only [hratio]
  have hmass : massFactor Y * M ≤ 4 * M := mul_le_mul_of_nonneg_right hfactor hM
  -- Convert the actual endpoint estimate from log coordinates at Y ^ b.
  have hb : 1 < b := hd.trans hdb
  have hlogB : 1 ≤ b * log Y := by
    calc
      1 ≤ b := hb.le
      _ = b * 1 := (mul_one b).symm
      _ ≤ b * log Y := mul_le_mul_of_nonneg_left hlog (zero_lt_one.trans hb).le
  have hB : exp (b * log Y) = Y ^ b := by
    rw [rpow_def_of_pos hY0, mul_comm b (log Y)]
  have htail : weightedTail psiErrorKernel (Y ^ b) = Jpsi (Y ^ b) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact weighted_eq t
  have hdefectY : |endpointDefect psiErrorKernel (Y ^ b)| ≤
      C * exp (-alpha * (b * log Y)) / (b * log Y) := by
    change |Q (Y ^ b) - a (Y ^ b) * weightedTail psiErrorKernel (Y ^ b)| ≤ _
    rw [htail, ← hB]
    exact hdefect (b * log Y) hlogB
  have hDupper : D ≤ C * exp (-alpha * (b * log Y)) := by
    calc
      _ ≤ |endpointDefect psiErrorKernel (Y ^ b)| := max_le (neg_le_abs _) (abs_nonneg _)
      _ ≤ C * exp (-alpha * (b * log Y)) / (b * log Y) := hdefectY
      _ ≤ _ := div_le_self (mul_nonneg hC (exp_nonneg _)) hlogB
  have hscale : sqrt (Y ^ d) * exp (-alpha * (b * log Y)) = Y ^ p := by
    rw [sqrt_eq_rpow (Y ^ d), ← rpow_mul hY0.le d (1 / 2),
      rpow_def_of_pos hY0 (d * (1 / 2)), ← exp_add, rpow_def_of_pos hY0 p]
    apply congrArg exp
    dsimp only [p]
    ring
  have hendpoint : 2 * (sqrt (Y ^ d) - sqrt Y) * D ≤ (1 / 4 : ℝ) * Y ^ s := by
    calc
      _ ≤ 2 * sqrt (Y ^ d) * D :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self _ (sqrt_nonneg Y)) (by norm_num)) hD
      _ ≤ 2 * sqrt (Y ^ d) * (C * exp (-alpha * (b * log Y))) :=
        mul_le_mul_of_nonneg_left hDupper (mul_nonneg (by norm_num) (sqrt_nonneg _))
      _ = 2 * C * (sqrt (Y ^ d) * exp (-alpha * (b * log Y))) := by ring
      _ = (1 / 4 : ℝ) * ((8 * C) * Y ^ p) := by
        rw [hscale]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hendGapY (by norm_num)
  have hlogCost : log (Y ^ d / Y) = (d - 1) * log Y := by
    rw [log_div (rpow_pos_of_pos hY0 _).ne' hY0.ne', log_rpow hY0]
    ring
  have hprimePower : 2 * K * log (Y ^ d / Y) ≤ (1 / 4 : ℝ) * Y ^ s := by
    rw [hlogCost, ← mul_assoc]
    have habs : |2 * K * (d - 1) * log Y| ≤ (1 / 4 : ℝ) * Y ^ s := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hY0.le s)] using hlogGapY
    exact (le_abs_self _).trans habs
  have htotal : Y ^ s ≤ massFactor Y * M +
      2 * (sqrt (Y ^ d) - sqrt Y) * D + 2 * K * log (Y ^ d / Y) := hprimeY.trans hupper
  have hpaid : (1 / 2 : ℝ) * Y ^ s ≤ 4 * M := by
    linarith only [htotal, hmass, hendpoint, hprimePower]
  change Y ^ r ≤ M
  linarith only [hpaid, hmassGapY]

/-- A positive seed strip gives the full lower power threshold at the
zero abscissa and bounds that abscissa from cofinal upper power estimates. -/
theorem weighted_negative_mass_power_criterion {alpha b : ℝ} (ha : 0 < alpha) :
    let data := fun z : ℂ => (IsNontrivialZero z, zeroAbscissa, weightedNegativeMass psiErrorKernel)
    (∀ z : ℂ, (data z).1 → z.re ≤ 1 - alpha) → 1 < b →
    (∀ r : ℝ, 0 < r → r < b * ((data 0).2.1 - 1 / 2) →
      ∀ᶠ Y : ℝ in atTop, Y ^ r ≤ (data 0).2.2 Y (Y ^ b)) ∧
    (∀ p C : ℝ, 0 ≤ p →
      (∃ᶠ Y : ℝ in atTop, (data 0).2.2 Y (Y ^ b) ≤ C * Y ^ p) →
      (data 0).2.1 ≤ 1 / 2 + p / b) := by
  intro data hstrip hb
  dsimp only [data] at hstrip ⊢
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hseed : zeroAbscissa ≤ 1 - alpha := by
    apply csSup_le zero_real_parts_nonempty
    rintro _ ⟨z, hz, rfl⟩
    exact hstrip z hz
  have hlower : ∀ r : ℝ, 0 < r → r < b * (zeroAbscissa - 1 / 2) →
      ∀ᶠ Y : ℝ in atTop, Y ^ r ≤ weightedNegativeMass psiErrorKernel Y (Y ^ b) := by
    intro r hr hrb
    let σ : ℝ := zeroAbscissa - 1 / 2
    have hσ : 0 < σ := by
      by_contra! h
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hb0.le h)) (hr.trans hrb)
    let gap : ℝ := max 1 (r / σ)
    have hgap : gap < b := max_lt hb ((div_lt_iff₀ hσ).mpr hrb)
    obtain ⟨d, hd, hdb⟩ := exists_between hgap
    have hd1 : 1 < d := (le_max_left _ _).trans_lt hd
    have hd0 : 0 < d := zero_lt_one.trans hd1
    have hrd : r < d * σ := (div_lt_iff₀ hσ).mp ((le_max_right _ _).trans_lt hd)
    let width : ℝ := 1 - zeroAbscissa
    have hwidth : 0 < width := by dsimp [width]; linarith only [ha, hseed]
    have hendpoint : d / 2 - b * width < d * σ := by
      dsimp only [width, σ]
      nlinarith only [mul_pos (sub_pos.mpr hdb) hwidth]
    let q : ℝ := max r (max (d / 2 - b * width) 0)
    have hq : q < d * σ := max_lt hrd (max_lt hendpoint (mul_pos hd0 hσ))
    have hq0 : 0 < q := hr.trans_le (le_max_left _ _)
    have hnear : 1 / 2 + q / d < zeroAbscissa := by
      have hdiv : q / d < σ := (div_lt_iff₀ hd0).mpr (by rwa [mul_comm])
      dsimp only [σ] at hdiv
      linarith only [hdiv]
    obtain ⟨_, ⟨rho, hzero, rfl⟩, hrho⟩ :=
      exists_lt_of_lt_csSup zero_real_parts_nonempty hnear
    have hβ : 1 / 2 < rho.re := lt_trans (lt_add_of_pos_right _ (div_pos hq0 hd0)) hrho
    have hdiv : q / d < rho.re - 1 / 2 := by linarith only [hrho]
    have hpole : q < d * (rho.re - 1 / 2) := by
      rw [mul_comm d]
      exact (div_lt_iff₀ hd0).mp hdiv
    exact off_line_zero_forces_weighted_negative_mass_of_actual_strip hwidth
      (fun z hz => by dsimp only [width]; linarith only [zero_re_le_abscissa hz])
      hd1 hdb hzero hβ hpole
  refine ⟨hlower, ?_⟩
  intro p C hp hsmall
  by_contra! hbad
  have hpb : p < b * (zeroAbscissa - 1 / 2) := by
    have := (div_lt_iff₀ hb0).mp (show p / b < zeroAbscissa - 1 / 2 by linarith only [hbad])
    simpa only [mul_comm] using this
  obtain ⟨r, hpr, hrb⟩ := exists_between hpb
  have hmid : p < (p + r) / 2 := by linarith only [hpr]
  have hmr : (p + r) / 2 < r := by linarith only [hpr]
  obtain ⟨Y, hsmallY, hlowerY, hscaleY, hY⟩ := (hsmall.and_eventually
    ((hlower r (hp.trans_lt hpr) hrb).and
      ((eventually_const_mul_rpow_le_rpow hmid C).and (eventually_gt_atTop (1 : ℝ))))).exists
  exact (not_lt_of_ge (hlowerY.trans (hsmallY.trans hscaleY)))
    (rpow_lt_rpow_of_exponent_lt hY hmr)

#print axioms off_line_zero_forces_weighted_negative_mass_of_actual_strip
#print axioms weighted_negative_mass_power_criterion

end D5.S3.Arith.Robin.Analytic.RobinWindowSharpLower
