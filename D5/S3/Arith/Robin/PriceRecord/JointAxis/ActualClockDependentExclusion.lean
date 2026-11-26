/- GID: D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Literal Robin budget labels have multiplicatively independent joint logarithm bases. -/
import D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm
import D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Transport of rational dependence to the literal three-axis clock budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion

open Real Filter
open scoped Topology
open D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover (jointSquare)
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
  (boxSizes coordinates floor_budget_errors transportConstant)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature (d)
open D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock (reference reference_pos reference_tendsto)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic (fixed_layer_root_offset_tendsto)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff (cutoff)
open D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm (omegaThree)
open D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm
  (eventually_clock_joint_logarithm)
open D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
  (RationalPowerIndependent dependent_clock_abs_lower)

/-- The first two literal floor-budget labels have positive natural representatives
with uniform bounds in the actual clock scale. -/
theorem eventually_clock_label_sizes {β κζ : ℝ}
    (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ) :
    ∀ᶠ e : ℤ in atTop,
      ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
        let R := reference e
        let Y := exp R
        |R - Lbar| ≤ 1 → 1 ≤ h →
        jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ (43 : ℝ) / 9 →
        ∃ H P Q : ℕ, (H : ℤ) = h ∧ (P : ℤ) = p 0 ∧ (Q : ℤ) = p 1 ∧
          0 < H ∧ 2 * H ≤ P ∧ H ≤ Q ∧ Q ≤ 3 * H ∧ (P : ℝ) ≤ 3 * R * H := by
  let K := transportConstant κζ
  let ρ := log 3 / log 2
  have hc : 0 < log 2 := log_pos (by norm_num)
  have hρlo : 3 / 2 < ρ := by
    have he := log_lt_log (by positivity : 0 < (2 : ℝ) ^ (3 : ℕ))
      (by norm_num : (2 : ℝ) ^ (3 : ℕ) < (3 : ℝ) ^ (2 : ℕ))
    rw [log_pow, log_pow] at he
    norm_num only [Nat.cast_ofNat] at he
    exact (lt_div_iff₀ hc).2 (by linarith only [he])
  have hρhi : ρ < 2 := by
    have he := log_lt_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) < (2 : ℝ) ^ (2 : ℕ))
    rw [log_pow] at he
    norm_num only [Nat.cast_ofNat] at he
    exact (div_lt_iff₀ hc).2 he
  have hY : Tendsto (fun e : ℤ => exp (reference e)) atTop atTop :=
    tendsto_exp_atTop.comp reference_tendsto
  have ha := (fixed_layer_root_offset_tendsto (j := 2) (by decide)).comp hY
  have hb := (fixed_layer_root_offset_tendsto (j := 3) (by decide)).comp hY
  have hrat : Tendsto (fun e : ℤ => d 3 (exp (reference e)) / d 2 (exp (reference e)))
      atTop (𝓝 ρ) := by
    change Tendsto (fun e : ℤ =>
      ((3 : ℝ) * log (cutoff 3 (referencePrice (exp (reference e)))) - log (exp (reference e))) /
      ((2 : ℝ) * log (cutoff 2 (referencePrice (exp (reference e)))) - log (exp (reference e))))
      atTop (𝓝 (log 3 / log 2))
    exact hb.div ha hc.ne'
  have hdec : Tendsto (fun R : ℝ => K * exp (-(R / 15))) atTop (𝓝 0) := by
    have hR : Tendsto (fun R : ℝ => (1 / 15 : ℝ) * R) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    have he := (tendsto_exp_neg_atTop_nhds_zero.comp hR).const_mul K
    simpa only [mul_zero, Function.comp_def,
      show ∀ x : ℝ, (1 / 15 : ℝ) * x = x / 15 from fun x => by ring] using he
  filter_upwards [reference_tendsto.eventually_ge_atTop (4 : ℝ),
    reference_tendsto.eventually_ge_atTop (1 + 2 / κζ),
    ha.eventually (eventually_gt_nhds (show (1 / 2 : ℝ) < log 2 from
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans log_two_gt_d9)),
    ha.eventually (eventually_lt_nhds (show log 2 < (1 : ℝ) from
      log_two_lt_d9.trans (by norm_num))),
    hrat.eventually (eventually_gt_nhds hρlo), hrat.eventually (eventually_lt_nhds hρhi),
    (hdec.comp reference_tendsto).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with e hR4 hRκ haLo haHi hrLo hrHi hSmall
  intro Lbar w h p R Y
  let a := d 2 Y
  let r := d 3 Y / a
  intro hclose hh hlabel
  change 4 ≤ R at hR4
  change 1 + 2 / κζ ≤ R at hRκ
  change 1 / 2 < a at haLo
  change a < 1 at haHi
  change 3 / 2 < r at hrLo
  change r < 2 at hrHi
  change K * exp (-(R / 15)) < 1 / 2 at hSmall
  have hR : 0 < R := reference_pos e
  have hR1 : 1 ≤ R := by linarith only [hR4]
  have haPos : 0 < a := by linarith only [haLo]
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) ≤ h := by linarith only [hhR]
  have hsLo : R ≤ R / a := by
    apply (le_div_iff₀ haPos).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left haHi.le hR.le
  have hsHi : R / a ≤ 2 * R := by
    apply (div_le_iff₀ haPos).2
    calc
      R = (2 * R) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left haLo.le (by positivity)
  have hbud := floor_budget_errors (β := β) (κζ := κζ) (X := Y) (Lbar := Lbar)
    (w := w) (h := h) (p := p) hβ hκζ
    (by simpa only [Y, log_exp] using (show (2 : ℝ) ≤ R by linarith only [hR4]))
    (by simpa only [Y, log_exp] using hRκ)
    (by simpa only [Y, log_exp] using hclose) hlabel
  have hpErr : |(p 0 : ℝ) - (h : ℝ) * (R / a)| ≤ K * exp (-(R / 15)) := by
    rw [abs_sub_comm]
    simpa only [Y, log_exp] using hbud.1
  have hqErr : |(p 1 : ℝ) - (h : ℝ) * r| ≤ K * exp (-(R / 15)) / R ^ 2 := by
    rw [abs_sub_comm]
    simpa only [Y, log_exp] using hbud.2
  have hE : 0 ≤ K * exp (-(R / 15)) := (abs_nonneg _).trans hpErr
  have hqHalf := (hqErr.trans (div_le_self hE (one_le_pow₀ hR1))).trans hSmall.le
  have hplo := mul_le_mul_of_nonneg_left hsLo hh0
  have hphi := mul_le_mul_of_nonneg_left hsHi hh0
  have hRh := mul_le_mul_of_nonneg_left hR4 hh0
  have hRh1 := mul_le_mul_of_nonneg_left hhR hR.le
  have hpLo : 2 * (h : ℝ) ≤ (p 0 : ℝ) := by
    linarith only [(abs_le.mp (hpErr.trans hSmall.le)).1, hplo, hRh, hhR]
  have hpHi : (p 0 : ℝ) ≤ 3 * R * (h : ℝ) := by
    nlinarith only [(abs_le.mp (hpErr.trans hSmall.le)).2, hphi, hRh1, hR1]
  have hqlo := mul_le_mul_of_nonneg_left hrLo.le hh0
  have hqhi := mul_le_mul_of_nonneg_left hrHi.le hh0
  have hqLo : (h : ℝ) ≤ (p 1 : ℝ) := by linarith only [(abs_le.mp hqHalf).1, hqlo, hhR]
  have hqHi : (p 1 : ℝ) ≤ 3 * (h : ℝ) := by linarith only [(abs_le.mp hqHalf).2, hqhi, hhR]
  have hp0 : 0 ≤ p 0 := by exact_mod_cast (show (0 : ℝ) ≤ (p 0 : ℝ) by linarith only [hpLo, hhR])
  have hq0 : 0 ≤ p 1 := by exact_mod_cast (show (0 : ℝ) ≤ (p 1 : ℝ) by linarith only [hqLo, hhR])
  have hH := Int.toNat_of_nonneg (show 0 ≤ h by omega)
  have hP := Int.toNat_of_nonneg hp0
  have hQ := Int.toNat_of_nonneg hq0
  have hHR : (h.toNat : ℝ) = (h : ℝ) := by exact_mod_cast hH
  have hPR : ((p 0).toNat : ℝ) = (p 0 : ℝ) := by exact_mod_cast hP
  have hQR : ((p 1).toNat : ℝ) = (p 1 : ℝ) := by exact_mod_cast hQ
  refine ⟨h.toNat, (p 0).toNat, (p 1).toNat, hH, hP, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < (h.toNat : ℝ) by rw [hHR]; linarith only [hhR])
  · exact_mod_cast (show 2 * (h.toNat : ℝ) ≤ ((p 0).toNat : ℝ) by rwa [hHR, hPR])
  · exact_mod_cast (show (h.toNat : ℝ) ≤ ((p 1).toNat : ℝ) by rwa [hHR, hQR])
  · exact_mod_cast (show ((p 1).toNat : ℝ) ≤ 3 * (h.toNat : ℝ) by rwa [hHR, hQR])
  · simpa only [hHR, hPR] using hpHi

private theorem eventually_log_raw_numerator_le :
    ∀ᶠ R : ℝ in atTop,
      ∀ {H P : ℕ}, 0 < H → (H : ℝ) ≤ exp (R / 50) →
        0 < P → (P : ℝ) ≤ 3 * R * H → log (2 * (P : ℝ)) ≤ R := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall, eventually_ge_atTop (max 1 (4 * log 6))] with R hsmall hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have h6 : log 6 ≤ R / 4 := by linarith only [(le_max_right 1 _).trans hR]
  change ‖log R‖ ≤ (1 / 2 : ℝ) * ‖R‖ at hsmall
  rw [Real.norm_eq_abs, abs_of_nonneg (log_nonneg hR1),
    Real.norm_eq_abs, abs_of_pos hR0] at hsmall
  intro H P hH hden hP hp
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogH : log (H : ℝ) ≤ R / 50 := by
    simpa only [log_exp] using log_le_log hH0 hden
  calc
    log (2 * (P : ℝ)) ≤ log ((6 * R) * (H : ℝ)) :=
      log_le_log (by positivity) (by linarith only [hp])
    _ = log 6 + log R + log (H : ℝ) := by
      rw [log_mul (by positivity : (6 * R : ℝ) ≠ 0) hH0.ne', log_mul (by norm_num) hR0.ne']
    _ ≤ R := by linarith only [h6, hsmall, hlogH, hR0]

/-- At all sufficiently large actual integer clock heights, every literal
budget label through the full exponential range has independent rational bases. -/
theorem eventually_actual_clock_independent {β κζ : ℝ}
    (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ) :
    ∀ᶠ e : ℤ in atTop,
      ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
        let R := reference e
        let Y := exp R
        |R - Lbar| ≤ 1 → 1 ≤ h → (h : ℝ) ≤ exp (R / 50) →
        jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ (43 : ℝ) / 9 →
        RationalPowerIndependent
          (3 * (p 0 : ℚ) / ((p 0 : ℚ) + (p 1 : ℚ)))
          (2 * (p 0 : ℚ) / ((p 0 : ℚ) + (h : ℚ))) := by
  let C := 50 * transportConstant κζ + 1
  let c := log (4 / 3) * log 2
  have hC : 0 < C := by unfold C transportConstant; positivity
  have hc : 0 < c := mul_pos (log_pos (by norm_num)) (log_pos (by norm_num))
  filter_upwards [eventually_clock_label_sizes hβ hκζ, eventually_clock_joint_logarithm hβ hκζ,
    reference_tendsto.eventually eventually_log_raw_numerator_le,
    reference_tendsto.eventually_gt_atTop (C / c)] with e hsize hΩ hlog hScale
  intro Lbar w h p R Y hclose hh hden hlabel
  by_contra hdep
  have hR : 0 < R := reference_pos e
  obtain ⟨H, P, Q, hH, hP, hQ, hH0, hp2, _, hq3, hpR⟩ := hsize hclose hh hlabel
  obtain ⟨hne, hup⟩ := hΩ hclose hh hden hlabel
  have hHR : (H : ℝ) = (h : ℝ) := by exact_mod_cast hH
  have hPR : (P : ℝ) = (p 0 : ℝ) := by exact_mod_cast hP
  have hQR : (Q : ℝ) = (p 1 : ℝ) := by exact_mod_cast hQ
  have hHQ : (H : ℚ) = (h : ℚ) := by exact_mod_cast hH
  have hPQ : (P : ℚ) = (p 0 : ℚ) := by exact_mod_cast hP
  have hQQ : (Q : ℚ) = (p 1 : ℚ) := by exact_mod_cast hQ
  have hlow := dependent_clock_abs_lower hH0 hp2 hq3
    (by simpa only [hHR, hPR, hQR] using hne)
    (by simpa only [hHQ, hPQ, hQQ] using hdep)
  have hlogP : log (2 * (P : ℝ)) ≤ R :=
    hlog hH0 (by simpa only [hHR] using hden) (by omega) hpR
  have hlog0 : 0 < log (2 * (P : ℝ)) := by
    apply log_pos
    have h : (2 : ℝ) ≤ P := by exact_mod_cast (show 2 ≤ P by omega)
    linarith only [h]
  have hlow' : c / R ≤ |omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ)| :=
    (div_le_div_of_nonneg_left hc.le hlog0 hlogP).trans
      (by simpa only [c, hHR, hPR, hQR] using hlow)
  have hupper : C * exp (-(R / 15)) / R ^ 2 < c / R := by
    have he : exp (-(R / 15)) ≤ 1 := by
      rw [← exp_zero]
      exact exp_le_exp.mpr (by linarith only [hR])
    have hCR : C < c * R := by
      have he' := (div_lt_iff₀ hc).1 (show C / c < R from hScale)
      simpa only [mul_comm] using he'
    apply (div_lt_iff₀ (pow_pos hR 2)).2
    calc
      _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC.le
      _ < c * R := hCR
      _ = _ := by field_simp [hR.ne'] <;> ring
  exact (not_lt_of_ge hlow') (hup.trans_lt hupper)

end D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion
