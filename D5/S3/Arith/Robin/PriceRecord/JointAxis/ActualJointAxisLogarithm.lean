/- GID: D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: The nonzero joint logarithm at the literal Robin clock budgets. -/
import D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
import D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The joint logarithm at all sufficiently large literal Robin clock budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm

open Real Filter
open D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm (omegaThree omegaThree_ne_zero_int
  abs_omegaThree_sub_le omegaThree_at_root_phases)
open scoped Topology
open D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover (jointSquare)
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
  (boxSizes coordinates floor_budget_errors transportConstant)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
  (d η F actual_root_equation normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock
  (reference reference_pos reference_tendsto)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic (fixed_layer_root_offset_tendsto)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff (cutoff)

private theorem root_residual {j : ℕ} (hj : 2 ≤ j) :
    ∀ᶠ e : ℤ in atTop,
      let R := reference e
      let a := d j (exp R)
      0 < a ∧ F R a = log (j : ℝ) + η j (exp R) ∧
        |η j (exp R)| ≤ 2 * exp (-(R / (j : ℝ))) ∧ η j (exp R) ≤ 0 := by
  have hX : Tendsto (fun e : ℤ => exp (reference e)) atTop atTop :=
    tendsto_exp_atTop.comp reference_tendsto
  filter_upwards [hX.eventually (actual_root_equation hj)] with e he
  let R := reference e
  let a := d j (exp R)
  let u := cutoff j (referencePrice (exp R))
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hroot : 0 < a ∧ 2 < u ∧ F R a = log (j : ℝ) + η j (exp R) := by
    simpa only [log_exp] using he
  obtain ⟨ha, hu, heq⟩ := hroot
  obtain ⟨_, _, hlow, hhigh⟩ := normalized_gain_bounds (j := j) (by omega) hu.le
  change -(2 : ℝ) / u ≤ η j (exp R) at hlow
  change η j (exp R) ≤ 0 at hhigh
  have hη : |η j (exp R)| ≤ 2 / u := by
    have hlow' : -(2 / u) ≤ η j (exp R) := by simpa only [neg_div] using hlow
    rw [abs_of_nonpos hhigh]
    linarith only [hlow']
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have haDef : a = (j : ℝ) * log u - R := by simp only [a, d, u, log_exp]
  have hlogu : log u = (R + a) / (j : ℝ) := by
    apply (eq_div_iff hj0.ne').2
    linarith only [haDef]
  have huEq : u = exp ((R + a) / (j : ℝ)) := by rw [← hlogu, exp_log hu0]
  change 0 < a ∧ F R a = log (j : ℝ) + η j (exp R) ∧
    |η j (exp R)| ≤ 2 * exp (-(R / (j : ℝ))) ∧ η j (exp R) ≤ 0
  refine ⟨ha, heq, hη.trans ?_, hhigh⟩
  rw [huEq, div_eq_mul_inv, ← exp_neg]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply exp_le_exp.mpr
  exact neg_le_neg (div_le_div_of_nonneg_right (by linarith only [ha]) hj0.le)

private theorem cone_log_ratio :
    11 / 7 < log 3 / log 2 ∧ log 3 / log 2 < 8 / 5 := by
  have hc : 0 < log 2 := log_pos (by norm_num)
  have hlo := log_lt_log (by positivity : 0 < (2 : ℝ) ^ (11 : ℕ))
    (by norm_num : (2 : ℝ) ^ (11 : ℕ) < (3 : ℝ) ^ (7 : ℕ))
  have hhi := log_lt_log (by positivity : 0 < (3 : ℝ) ^ (5 : ℕ))
    (by norm_num : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ))
  rw [log_pow, log_pow] at hlo hhi
  norm_num only [Nat.cast_ofNat] at hlo hhi
  exact ⟨(lt_div_iff₀ hc).mpr (by linarith only [hlo]),
    (div_lt_iff₀ hc).mpr (by linarith only [hhi])⟩

/-- At all sufficiently large literal B = 0 clock heights the first two
floor-budget labels yield a nonzero joint form with inverse-square precision. -/
theorem eventually_clock_joint_logarithm {β κζ : ℝ}
    (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ) :
    ∀ᶠ e : ℤ in atTop,
      ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
        let R := reference e
        let Y := exp R
        let K := transportConstant κζ
        |R - Lbar| ≤ 1 → 1 ≤ h → (h : ℝ) ≤ exp (R / 50) →
        jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ (43 : ℝ) / 9 →
        let Ω := omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ)
        Ω ≠ 0 ∧ |Ω| ≤ (50 * K + 1) * exp (-(R / 15)) / R ^ 2 := by
  let K := transportConstant κζ
  let ρ := log 3 / log 2
  let ε := min (ρ - 11 / 7) (8 / 5 - ρ) / 2
  have hc : 0 < log 2 := log_pos (by norm_num)
  have hK : 0 < K := by unfold K transportConstant; positivity
  have hLimLo : 11 / 7 < ρ := cone_log_ratio.1
  have hLimHi : ρ < 8 / 5 := cone_log_ratio.2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr hLimLo) (sub_pos.mpr hLimHi))
  have hρlo : 11 / 7 + ε < ρ := by
    have hm := min_le_left (ρ - 11 / 7) (8 / 5 - ρ)
    change 11 / 7 + min (ρ - 11 / 7) (8 / 5 - ρ) / 2 < ρ
    linarith only [hm, hLimLo]
  have hρhi : ρ < 8 / 5 - ε := by
    have hm := min_le_right (ρ - 11 / 7) (8 / 5 - ρ)
    change ρ < 8 / 5 - min (ρ - 11 / 7) (8 / 5 - ρ) / 2
    linarith only [hm, hLimHi]
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
  have hdec :
      Tendsto (fun R : ℝ => K * exp (-(R / 15))) atTop (𝓝 0) := by
    have hR : Tendsto (fun R : ℝ => (1 / 15 : ℝ) * R) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    have hh := (tendsto_exp_neg_atTop_nhds_zero.comp hR).const_mul K
    simpa only [mul_zero, Function.comp_def, show ∀ x : ℝ, (1 / 15 : ℝ) * x = x / 15 from
      fun x => by ring] using hh
  have hresDecay :
      Tendsto (fun R : ℝ => 6 * R ^ 2 * exp (-(37 / 150 : ℝ) * R)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (37 / 150) (by norm_num)).const_mul 6
    simpa only [mul_zero, mul_assoc, Real.rpow_two, neg_mul] using hh
  filter_upwards [reference_tendsto.eventually_ge_atTop (4 : ℝ),
    reference_tendsto.eventually_ge_atTop (1 + 2 / κζ),
    root_residual (j := 2) (by decide), root_residual (j := 3) (by decide),
    hrat.eventually (eventually_gt_nhds hρlo), hrat.eventually (eventually_lt_nhds hρhi),
    (hdec.comp reference_tendsto).eventually (eventually_lt_nhds (lt_min hε (by norm_num : (0 : ℝ) < 1 / 2))),
    (hresDecay.comp reference_tendsto).eventually (eventually_lt_nhds zero_lt_one)]
    with e hR4 hRκ hroot₂ hroot₃ hrlo hrhi hsmall hdecR
  intro Lbar w h p
  let R := reference e
  let Y := exp R
  let a := d 2 Y
  let b := d 3 Y
  let s := R / a
  let r := b / a
  let E := exp (-(R / 15))
  change ∀ (_ : |R - Lbar| ≤ 1) (_ : 1 ≤ h) (_ : (h : ℝ) ≤ exp (R / 50))
    (_ : jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ (43 : ℝ) / 9),
    omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ) ≠ 0 ∧
    |omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ)| ≤ (50 * K + 1) * E / R ^ 2
  intro hclose hh hden hlabel
  change 4 ≤ R at hR4
  change 11 / 7 + ε < r at hrlo
  change r < 8 / 5 - ε at hrhi
  change K * E < min ε (1 / 2) at hsmall
  change 6 * R ^ 2 * exp (-(37 / 150 : ℝ) * R) < 1 at hdecR
  have hR : 0 < R := reference_pos e
  have hR2 : 0 < R ^ 2 := pow_pos hR _
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith only [hh1]
  have hr₁ : 3 / 2 ≤ r := by linarith only [hrlo, hε]
  have hr₂ : r ≤ 2 := by linarith only [hrhi, hε]
  have haEq : 0 < a ∧ a + log (1 + a / R) = log 2 + η 2 Y ∧
      |η 2 Y| ≤ 2 * exp (-(R / 2)) ∧ η 2 Y ≤ 0 := by
    simpa only [F, Nat.cast_ofNat] using hroot₂
  have hbEq : 0 < b ∧ b + log (1 + b / R) = log 3 + η 3 Y ∧
      |η 3 Y| ≤ 2 * exp (-(R / 3)) ∧ η 3 Y ≤ 0 := by
    simpa only [F, Nat.cast_ofNat] using hroot₃
  have hs : R ≤ s := by
    have haOne : a ≤ 1 := by
      have hla := log_nonneg (show (1 : ℝ) ≤ 1 + a / R by
        linarith only [div_pos haEq.1 hR])
      have hc1 := log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      linarith only [hla, hc1, haEq.2.2.2, haEq.2.1]
    apply (le_div_iff₀ haEq.1).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left haOne hR.le
  have hbud := floor_budget_errors (β := β) (κζ := κζ) (X := Y) (Lbar := Lbar)
    (w := w) (h := h) (p := p) hβ hκζ
    (by simpa only [Y, log_exp] using (show (2 : ℝ) ≤ R by linarith only [hR4]))
    (by simpa only [Y, log_exp] using hRκ)
    (by simpa only [Y, log_exp] using hclose) hlabel
  have hp : |(p 0 : ℝ) - (h : ℝ) * s| ≤ K * E := by
    rw [abs_sub_comm]
    simpa only [Y, log_exp] using hbud.1
  have hq : |(p 1 : ℝ) - (h : ℝ) * r| ≤ K * E / R ^ 2 := by
    rw [abs_sub_comm]
    simpa only [Y, log_exp] using hbud.2
  have hR1 : 1 ≤ R := by linarith only [hR4]
  have hsquare : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hqe : |(p 1 : ℝ) - (h : ℝ) * r| ≤ K * E :=
    hq.trans (div_le_self (by positivity) hsquare)
  have hpHalf := hp.trans (hsmall.le.trans (min_le_right _ _))
  have hqHalf := hqe.trans (hsmall.le.trans (min_le_right _ _))
  have hpLarge : (h : ℝ) < (p 0 : ℝ) := by
    have hRh := mul_le_mul_of_nonneg_left hs hh0.le
    have hfour := mul_le_mul_of_nonneg_left hR4 hh0.le
    linarith only [(abs_le.mp hpHalf).1, hRh, hfour, hh1]
  have hqe' := hqe.trans (hsmall.le.trans (min_le_left _ _))
  have hεh : ε ≤ (h : ℝ) * ε := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh1 hε.le
  have hloReal : 11 * (h : ℝ) < 7 * (p 1 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hrlo hh0
    nlinarith only [h, hεh, (abs_le.mp hqe').1]
  have hhiReal : 5 * (p 1 : ℝ) < 8 * (h : ℝ) := by
    have h := mul_lt_mul_of_pos_left hrhi hh0
    nlinarith only [h, hεh, (abs_le.mp hqe').2]
  refine ⟨omegaThree_ne_zero_int (by omega) (by exact_mod_cast hpLarge)
    (by exact_mod_cast hloReal) (by exact_mod_cast hhiReal), ?_⟩
  have hMove := abs_omegaThree_sub_le hh1 hR4 hs hr₁ hr₂ hpHalf hqHalf
  have hCenter := omegaThree_at_root_phases hh0 hR haEq.1 hbEq.1 haEq.2.1 hbEq.2.1
  change omegaThree (h : ℝ) ((h : ℝ) * s) ((h : ℝ) * r) =
    (h : ℝ) * (r * η 2 Y - η 3 Y) at hCenter
  have hExpOrder : exp (-(R / 2)) ≤ exp (-(R / 3)) :=
    exp_le_exp.mpr (by linarith only [hR])
  have hInner : |r * η 2 Y - η 3 Y| ≤ 6 * exp (-(R / 3)) := calc
    _ ≤ |r * η 2 Y| + |η 3 Y| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (r * η 2 Y) 0 (η 3 Y)
    _ ≤ 2 * (2 * exp (-(R / 3))) + 2 * exp (-(R / 3)) := by
      rw [abs_mul, abs_of_nonneg (by linarith only [hr₁] : 0 ≤ r)]
      exact add_le_add (mul_le_mul hr₂
        (haEq.2.2.1.trans (mul_le_mul_of_nonneg_left hExpOrder (by norm_num)))
        (abs_nonneg _) (by norm_num)) hbEq.2.2.1
    _ = _ := by ring
  have hSmallCenter : |omegaThree (h : ℝ) ((h : ℝ) * s) ((h : ℝ) * r)| ≤ E / R ^ 2 := by
    rw [hCenter, abs_mul, abs_of_pos hh0]
    calc
      _ ≤ exp (R / 50) * (6 * exp (-(R / 3))) :=
        mul_le_mul hden hInner (abs_nonneg _) (by positivity)
      _ = 6 * exp (-(37 / 150 : ℝ) * R) * E := by
        have hexps : exp (R / 50) * exp (-(R / 3)) =
            exp (-(37 / 150 : ℝ) * R) * E := by
          dsimp only [E]
          rw [← exp_add, ← exp_add]
          congr 1 <;> ring
        rw [← mul_assoc, mul_comm (exp (R / 50)) 6, mul_assoc, hexps, ← mul_assoc]
      _ ≤ _ := by
        apply (le_div_iff₀ hR2).2
        calc
          _ = (6 * R ^ 2 * exp (-(37 / 150 : ℝ) * R)) * E := by ring
          _ ≤ 1 * E := mul_le_mul_of_nonneg_right hdecR.le (by positivity)
          _ = E := one_mul E
  have hpow : R ^ 2 ≤ R ^ 3 := by
    rw [pow_succ R 2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hR1 hR2.le
  calc
    |omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ)| ≤
        |omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ) -
          omegaThree (h : ℝ) ((h : ℝ) * s) ((h : ℝ) * r)| +
        |omegaThree (h : ℝ) ((h : ℝ) * s) ((h : ℝ) * r)| := by
      simpa only [sub_zero] using abs_sub_le
        (omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ))
        (omegaThree (h : ℝ) ((h : ℝ) * s) ((h : ℝ) * r)) 0
    _ ≤ 48 / R ^ 3 * (K * E) + 2 * (K * E / R ^ 2) + E / R ^ 2 :=
      add_le_add (hMove.trans (add_le_add
        (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hq (by norm_num)))) hSmallCenter
    _ ≤ 48 / R ^ 2 * (K * E) + 2 * (K * E / R ^ 2) + E / R ^ 2 :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 48) hR2 hpow)
          (by positivity : 0 ≤ K * E)) le_rfl) le_rfl
    _ = _ := by ring

end D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm
