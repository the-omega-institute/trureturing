/- GID: D5/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ZeroFreeStripRobinWindow
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Negative Robin window mass and an actual zero strip give a finite step toward RH. -/

import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import Mathlib.Analysis.SpecificLimits.Basic

/-! On a fixed power window, the initial zero strip bounds the outer endpoint
payment. Subpower control of the interior mass improves the strip, and finitely
many such improvements reach the critical line. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi weighted_eq)
open D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope (actual_terminal_defect_exp_bound)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens.WeightedTailInverse (a)
open D5.S3.Weil.Mertens.WeightedTailWindowMass (endpointDefect weightedNegativeMass)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
  (robinBudget off_line_zero_forces_robin_budget)
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction (golden_right_half_strip_implies_rh)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Arith.Robin.Analytic.ZeroFreeStripRobinWindow

private lemma one_lt_of_exp_one_le {Y : ℝ} (hY : exp 1 ≤ Y) : 1 < Y :=
  (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hY

private lemma one_le_mul_log {Y b : ℝ} (hb : 1 < b) (hY : exp 1 ≤ Y) :
    1 ≤ b * log Y := by
  have hL : 1 ≤ log Y := by
    simpa only [log_exp] using log_le_log (exp_pos 1) hY
  calc
    1 ≤ b := hb.le
    _ = b * 1 := (mul_one b).symm
    _ ≤ b * log Y := mul_le_mul_of_nonneg_left hL (zero_lt_one.trans hb).le

/-- The initial strip bounds the endpoint payment at the left scale of every
sufficiently late power window, retaining the logarithmic denominator. -/
private lemma sqrt_mul_negative_endpoint_le_of_actual_strip {alpha b : ℝ}
    (ha : 0 < alpha) (hhalf : alpha ≤ 1 / 2)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha)
    (hb : 1 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, exp 1 ≤ Y →
      sqrt Y * max (-endpointDefect psiErrorKernel (Y ^ b)) 0 ≤
        C * Y ^ (1 / 2 - alpha * b) / (b * log Y) := by
  obtain ⟨C, hC, hE⟩ := actual_terminal_defect_exp_bound ha hhalf hstrip
  refine ⟨C, hC, ?_⟩
  intro Y hY
  have hY0 : 0 < Y := (exp_pos 1).trans_le hY
  have hpow : exp (b * log Y) = Y ^ b := by
    rw [rpow_def_of_pos hY0, mul_comm b (log Y)]
  have htail : weightedTail psiErrorKernel (Y ^ b) = Jpsi (Y ^ b) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact weighted_eq t
  have hend : |endpointDefect psiErrorKernel (Y ^ b)| ≤
      C * exp (-alpha * (b * log Y)) / (b * log Y) := by
    change |Q (Y ^ b) - a (Y ^ b) * weightedTail psiErrorKernel (Y ^ b)| ≤ _
    rw [htail, ← hpow]
    exact hE (b * log Y) (one_le_mul_log hb hY)
  have hscale : sqrt Y * exp (-alpha * (b * log Y)) = Y ^ (1 / 2 - alpha * b) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hY0 (1 / 2), ← exp_add,
      rpow_def_of_pos hY0 (1 / 2 - alpha * b)]
    congr 1 <;> ring
  calc
    _ ≤ sqrt Y * |endpointDefect psiErrorKernel (Y ^ b)| :=
      mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _)) (sqrt_nonneg Y)
    _ ≤ sqrt Y * (C * exp (-alpha * (b * log Y)) / (b * log Y)) :=
      mul_le_mul_of_nonneg_left hend (sqrt_nonneg Y)
    _ = C * (sqrt Y * exp (-alpha * (b * log Y))) / (b * log Y) := by ring
    _ = _ := by rw [hscale]

/-- Under the width condition the endpoint payment tends to zero, including
at equality where the logarithmic denominator supplies the decay. -/
theorem tendsto_sqrt_mul_negative_endpoint_of_actual_strip {alpha b : ℝ}
    (ha : 0 < alpha) (hhalf : alpha ≤ 1 / 2)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha)
    (hb : 1 < b) (hwidth : 1 / 2 ≤ alpha * b) :
    Tendsto (fun Y : ℝ => sqrt Y * max (-endpointDefect psiErrorKernel (Y ^ b)) 0)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hE⟩ := sqrt_mul_negative_endpoint_le_of_actual_strip ha hhalf hstrip hb
  have hlog : Tendsto (fun Y : ℝ => b * log Y) atTop atTop :=
    Tendsto.const_mul_atTop (zero_lt_one.trans hb) Real.tendsto_log_atTop
  have hmajor : Tendsto (fun Y : ℝ => C / (b * log Y)) atTop (𝓝 0) :=
    hlog.const_div_atTop C
  refine squeeze_zero' (Eventually.of_forall fun Y =>
    mul_nonneg (sqrt_nonneg Y) (le_max_right _ _)) ?_ hmajor
  filter_upwards [eventually_ge_atTop (exp 1)] with Y hY
  have hpow : Y ^ (1 / 2 - alpha * b) ≤ 1 := by
    simpa only [rpow_zero] using
      (rpow_le_rpow_of_exponent_le (one_lt_of_exp_one_le hY).le (sub_nonpos.mpr hwidth))
  refine (hE Y hY).trans ?_
  apply div_le_div_of_nonneg_right _ (zero_le_one.trans (one_le_mul_log hb hY))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC

/-- Subpower interior mass on arbitrarily late windows of a fixed width
improves the actual zero strip by the outer exponent, capped at the critical
line. The endpoint estimate uses only the starting strip. -/
theorem actual_strip_improvement_of_frequently_small_weighted_negative_mass {alpha b : ℝ}
    (ha : 0 < alpha) (hhalf : alpha ≤ 1 / 2)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha)
    (hb : 1 < b)
    (hwindows : ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop,
      weightedNegativeMass psiErrorKernel Y (Y ^ b) ≤ Y ^ η) :
    ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - min (1 / 2) (b * alpha) := by
  intro rho hrho
  by_contra! hbad
  have hβ : 1 / 2 < rho.re := by
    linarith only [hbad, min_le_left (1 / 2 : ℝ) (b * alpha)]
  let p : ℝ := max 0 (1 / 2 - b * alpha)
  have hp : 0 ≤ p := le_max_left _ _
  have hpβ : p < rho.re - 1 / 2 :=
    max_lt (sub_pos.mpr hβ) (by linarith only [hbad, min_le_right (1 / 2 : ℝ) (b * alpha)])
  obtain ⟨q, hpq, hqβ⟩ := exists_between hpβ
  let η : ℝ := (p + q) / 2
  have hpη : p < η := by dsimp only [η]; linarith only [hpq]
  have hηq : η < q := by dsimp only [η]; linarith only [hpq]
  have hζ : riemannZeta rho = 0 := hrho.1
  have hlower := off_line_zero_forces_robin_budget hζ hβ hrho.2.2 hb (sub_pos.mpr hqβ)
  rw [show rho.re - 1 / 2 - (rho.re - 1 / 2 - q) = q by ring] at hlower
  obtain ⟨C, hC, hE⟩ := sqrt_mul_negative_endpoint_le_of_actual_strip ha hhalf hstrip hb
  have hlarge : ∀ᶠ Y : ℝ in atTop, C + 1 < Y ^ (q - η) :=
    (tendsto_rpow_atTop (sub_pos.mpr hηq)).eventually_gt_atTop (C + 1)
  obtain ⟨Y, hmass, hlow, hY, hlargeY⟩ :=
    ((hwindows η (hp.trans_lt hpη)).and_eventually
      (hlower.and ((eventually_ge_atTop (exp 1)).and hlarge))).exists
  have hY0 : 0 < Y := (exp_pos 1).trans_le hY
  have hend : sqrt Y * max (-endpointDefect psiErrorKernel (Y ^ b)) 0 ≤ C * Y ^ η := by
    calc
      _ ≤ C * Y ^ (1 / 2 - alpha * b) / (b * log Y) := hE Y hY
      _ ≤ C * Y ^ (1 / 2 - alpha * b) :=
        div_le_self (mul_nonneg hC (rpow_nonneg hY0.le _)) (one_le_mul_log hb hY)
      _ ≤ C * Y ^ p :=
        mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_exponent_le (one_lt_of_exp_one_le hY).le
            (by simpa only [mul_comm alpha b] using
              (le_max_right 0 (1 / 2 - b * alpha)))) hC
      _ ≤ C * Y ^ η :=
        mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_exponent_le (one_lt_of_exp_one_le hY).le hpη.le) hC
  have hupper : robinBudget Y b < Y ^ q := by
    unfold robinBudget
    calc
      _ ≤ Y ^ η + C * Y ^ η := add_le_add hmass hend
      _ = (C + 1) * Y ^ η := by ring
      _ < Y ^ (q - η) * Y ^ η := mul_lt_mul_of_pos_right hlargeY (rpow_pos_of_pos hY0 _)
      _ = Y ^ q := by rw [← rpow_add hY0, sub_add_cancel]
  exact (not_lt_of_ge hlow) hupper

/-- Any strictly positive seed strip and the same interior mass hypothesis
for one fixed outer exponent suffice for RH. The strip widths are
`min (1 / 2) (b ^ n * alpha₀)` with the seed capped at `1 / 2`. -/
theorem rh_of_frequently_small_weighted_negative_mass_of_actual_strip {alpha b : ℝ}
    (ha : 0 < alpha)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha)
    (hb : 1 < b)
    (hwindows : ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop,
      weightedNegativeMass psiErrorKernel Y (Y ^ b) ≤ Y ^ η) :
    RiemannHypothesis := by
  let alpha₀ : ℝ := min (1 / 2) alpha
  have hseed : 0 < alpha₀ := lt_min (by norm_num) ha
  have hseedHalf : alpha₀ ≤ 1 / 2 := min_le_left _ _
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hcap : (1 / 2 : ℝ) ≤ b * (1 / 2) := by linarith only [hb]
  have hiter : ∀ n : ℕ, ∀ rho : ℂ, IsNontrivialZero rho →
      rho.re ≤ 1 - min (1 / 2) (b ^ n * alpha₀) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, one_mul, min_eq_right hseedHalf]
      intro rho hrho
      exact (hstrip rho hrho).trans (sub_le_sub_left (min_le_right (1 / 2 : ℝ) alpha) 1)
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      have hwidth : 0 < min (1 / 2 : ℝ) (b ^ n * alpha₀) :=
        lt_min (by norm_num) (mul_pos (pow_pos hb0 n) hseed)
      have hstep := actual_strip_improvement_of_frequently_small_weighted_negative_mass
        hwidth (min_le_left _ _) ih hb hwindows
      rw [mul_min_of_nonneg _ _ hb0.le, ← min_assoc, min_eq_left hcap] at hstep
      exact hstep
  have hpow : Tendsto (fun n : ℕ => b ^ n * alpha₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hb).atTop_mul_const hseed
  obtain ⟨n, hn⟩ := (hpow.eventually_ge_atTop (1 / 2)).exists
  apply golden_right_half_strip_implies_rh
  intro rho hz hright hlt
  have hrho : IsNontrivialZero rho := ⟨hz, by linarith only [hright], hlt⟩
  have hbound := hiter n rho hrho
  rw [min_eq_left hn] at hbound
  linarith only [hright, hbound]

end D5.S3.Arith.Robin.Analytic.ZeroFreeStripRobinWindow
