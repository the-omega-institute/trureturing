/- GID: D5/S0/Diagonal/MarginVanishing
   generality: G
   mirror-B: D5/B/S0/Diagonal/MarginVanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Corrected KL margin bounds vanish as address cardinality tends to infinity. -/

import D5.S0.Diagonal.MarginBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

universe u

namespace D5.S0.Diagonal.MarginVanishing

open MarginBound

/-- The corrected finite linear-margin union bound at address cardinality `a`. -/
noncomputable def linearMarginBound (y : ℕ) (alpha : ℝ) (a : ℕ) : ℝ :=
  (a : ℝ) * Real.exp (-((a : ℝ) - 1) *
    bernoulliKL (alpha * (a : ℝ) / ((a : ℝ) - 1)) (((y : ℝ) - 1) / (y : ℝ)))

private theorem tendsto_adjusted_margin (alpha : ℝ) :
    Tendsto (fun a : ℕ => alpha * (a : ℝ) / ((a : ℝ) - 1)) atTop (nhds alpha) := by
  have hden : Tendsto (fun a : ℕ => (a : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun a : ℕ => ((a : ℝ) - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto (fun a : ℕ => alpha + alpha * ((a : ℝ) - 1)⁻¹)
      atTop (nhds alpha) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 1] with a ha
  have hden_ne : (a : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < a := by exact_mod_cast ha
    linarith
  field_simp
  ring

/-- The corrected KL-Chernoff linear-margin bound vanishes as the address cardinality grows. -/
theorem linear_margin_bound_tendsto_zero (y : ℕ) (alpha : ℝ) (hy : 2 ≤ y)
    (halpha : 0 < alpha) (halpha_lt : alpha < ((y : ℝ) - 1) / (y : ℝ)) :
    Tendsto (linearMarginBound y alpha) atTop (nhds 0) := by
  let p := ((y : ℝ) - 1) / (y : ℝ)
  let c := bernoulliKL alpha p
  let b := c / 2
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast Nat.zero_lt_of_lt (by omega : 0 < y)
  have hy_one : (1 : ℝ) < y := by exact_mod_cast hy
  have hp_pos : 0 < p := by
    exact div_pos (sub_pos.mpr hy_one) hy_pos
  have hp_one : p < 1 := by
    rw [div_lt_one hy_pos]
    linarith
  have halpha_one : alpha < 1 := halpha_lt.trans hp_one
  have hc_pos : 0 < c := by
    exact bernoulliKL_pos halpha halpha_one hp_pos hp_one (ne_of_lt halpha_lt)
  have hb_pos : 0 < b := by positivity
  have hq := tendsto_adjusted_margin alpha
  have hkl : Tendsto
      (fun a : ℕ => bernoulliKL (alpha * (a : ℝ) / ((a : ℝ) - 1)) p)
      atTop (nhds c) := by
    exact (continuousAt_bernoulliKL halpha halpha_one hp_pos hp_one).tendsto.comp
      (hq.prodMk_nhds tendsto_const_nhds)
  have hmodel : Tendsto
      (fun a : ℕ => Real.exp b * ((a : ℝ) * Real.exp (-b * (a : ℝ))))
      atTop (nhds 0) := by
    have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb_pos).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, Real.rpow_one, mul_zero] using
      tendsto_const_nhds.mul hbase
  apply squeeze_zero'
  · exact Eventually.of_forall fun a =>
      mul_nonneg (Nat.cast_nonneg a) (Real.exp_pos _).le
  · filter_upwards [eventually_gt_atTop 1,
      hkl.eventually_const_lt (by dsimp [b]; linarith : b < c)] with a ha hrate
    have ha_real : (1 : ℝ) < a := by exact_mod_cast ha
    have hexponent :
        -((a : ℝ) - 1) *
            bernoulliKL (alpha * (a : ℝ) / ((a : ℝ) - 1)) p ≤
          b - b * (a : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hrate.le (sub_nonneg.mpr ha_real.le)]
    calc
      linearMarginBound y alpha a =
          (a : ℝ) * Real.exp (-((a : ℝ) - 1) *
            bernoulliKL (alpha * (a : ℝ) / ((a : ℝ) - 1)) p) := rfl
      _ ≤ (a : ℝ) * Real.exp (b - b * (a : ℝ)) := by gcongr
      _ = Real.exp b * ((a : ℝ) * Real.exp (-b * (a : ℝ))) := by
        rw [show b - b * (a : ℝ) = b + (-b * (a : ℝ)) by ring, Real.exp_add]
        ring
  · exact hmodel

/-- For a fixed finite value type, the actual margin-failure probability vanishes as the
address type `Fin a` grows. -/
theorem margin_failure_probability_tendsto_zero {Y : Type u} [Fintype Y] (f : Y → Y)
    (alpha : ℝ) (hY : 2 ≤ Fintype.card Y) (halpha : 0 < alpha)
    (halpha_lt : alpha < ((Fintype.card Y : ℝ) - 1) / Fintype.card Y) :
    Tendsto (fun a : ℕ => marginFailureProbability (A := Fin a) f alpha) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun a => by
      unfold marginFailureProbability
      positivity
  · have hq := tendsto_adjusted_margin alpha
    filter_upwards [eventually_gt_atTop 1, hq.eventually_lt_const halpha_lt]
      with a ha hqa
    have ha_two : 2 ≤ a := by omega
    simpa only [linearMarginBound, Fintype.card_fin] using
      linear_margin_bound (A := Fin a) f alpha
        (by simpa only [Fintype.card_fin] using ha_two) hY halpha
        (by simpa only [Fintype.card_fin] using hqa)
  · exact linear_margin_bound_tendsto_zero (Fintype.card Y) alpha hY halpha halpha_lt

end D5.S0.Diagonal.MarginVanishing
