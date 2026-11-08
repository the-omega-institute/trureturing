/- GID: D5/S1/Dynamics/Shadowing/RationalIntervalAction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/RationalIntervalAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive rational actions on the closed unit interval and their integer dynamics. -/

import D5.S1.Dynamics.Shadowing.RationalIntervalMarkers
import D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Order.Compact

/-! The multiplicative parameter acts by a rational formula, including both endpoints. -/

open Set Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.RationalInterval

abbrev I := Set.Icc (0 : ℝ) 1

/-- The closed-interval denominator stays strictly positive for every positive parameter. -/
theorem denominator_pos {c : ℝ} (hc : 0 < c) (u : I) :
    0 < 1 - (u : ℝ) + c * u := by
  have hcu := mul_nonneg hc.le u.property.1
  rcases lt_or_eq_of_le u.property.2 with h | h
  · linarith
  · rw [h]
    linarith

/-- The literal positive-parameter rational action on the entire closed interval. -/
noncomputable def action (c : ℝ) (hc : 0 < c) (u : I) : I :=
  ⟨c * u / (1 - (u : ℝ) + c * u),
    div_nonneg (mul_nonneg hc.le u.property.1) (denominator_pos hc u).le,
    (div_le_one (denominator_pos hc u)).mpr (by linarith [u.property.2])⟩

@[simp] theorem action_coe (c : ℝ) (hc : 0 < c) (u : I) :
    (action c hc u : ℝ) = c * u / (1 - (u : ℝ) + c * u) := rfl

private theorem continuous_action_parameter :
    Continuous (fun p : {c : ℝ // 0 < c} × I =>
      (action p.1.1 p.1.2 p.2 : ℝ)) := by
  apply Continuous.div
  · exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
  · intro p
    exact (denominator_pos p.1.2 p.2).ne'

/-- Joint continuity uses a positive denominator at every closed-interval point. -/
theorem continuous_action :
    Continuous (fun p : {c : ℝ // 0 < c} × I => action p.1.1 p.1.2 p.2) :=
  continuous_action_parameter.subtype_mk _

@[simp] theorem action_one (u : I) : action 1 (by norm_num) u = u := by
  apply Subtype.ext
  simp [action]

/-- Composition is multiplication of the positive rational parameters. -/
theorem action_mul (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (u : I) :
    action c hc (action d hd u) = action (c * d) (mul_pos hc hd) u := by
  apply Subtype.ext
  have h₁ := (denominator_pos hd u).ne'
  have h₂ := (denominator_pos hc (action d hd u)).ne'
  have h₃ := (denominator_pos (mul_pos hc hd) u).ne'
  simp only [action_coe] at h₂ ⊢
  apply (div_eq_div_iff h₂ h₃).mpr
  field_simp [h₁]
  <;> ring

/-- Every positive parameter gives a homeomorphism, with reciprocal parameter as inverse. -/
noncomputable def homeomorph (c : ℝ) (hc : 0 < c) : I ≃ₜ I where
  toFun := action c hc
  invFun := action c⁻¹ (inv_pos.mpr hc)
  left_inv u := by
    rw [action_mul]
    simpa [inv_mul_cancel₀ hc.ne'] using action_one u
  right_inv u := by
    rw [action_mul]
    simpa [mul_inv_cancel₀ hc.ne'] using action_one u
  continuous_toFun := continuous_action.comp
    ((continuous_const : Continuous (fun _ : I => (⟨c, hc⟩ : {c : ℝ // 0 < c}))).prodMk
      continuous_id)
  continuous_invFun := continuous_action.comp
    ((continuous_const : Continuous (fun _ : I =>
      (⟨c⁻¹, inv_pos.mpr hc⟩ : {c : ℝ // 0 < c}))).prodMk continuous_id)

@[simp] theorem homeomorph_apply (c : ℝ) (hc : 0 < c) (u : I) :
    homeomorph c hc u = action c hc u := rfl

@[simp] theorem homeomorph_one : homeomorph 1 (by norm_num) = 1 := by
  apply Homeomorph.ext
  intro u
  exact action_one u

theorem homeomorph_mul (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    homeomorph (c * d) (mul_pos hc hd) = homeomorph c hc * homeomorph d hd := by
  apply Homeomorph.ext
  intro u
  exact (action_mul c d hc hd u).symm

/-- Integer powers retain the same rational formula, including negative times. -/
theorem homeomorph_zpow (c : ℝ) (hc : 0 < c) (k : ℤ) :
    homeomorph c hc ^ k = homeomorph (c ^ k) (zpow_pos hc k) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, zpow_one, ih, ← homeomorph_mul]
    congr 1
  | pred n ih =>
    apply mul_left_cancel (a := homeomorph c hc)
    calc
      homeomorph c hc * homeomorph c hc ^ (-(n : ℤ) - 1) =
          homeomorph c hc ^ (-(n : ℤ)) := by
        simpa only [zpow_one, show (1 : ℤ) + (-(n : ℤ) - 1) = -(n : ℤ) by omega]
          using (zpow_add (homeomorph c hc) (1 : ℤ) (-(n : ℤ) - 1)).symm
      _ = homeomorph (c ^ (-(n : ℤ))) (zpow_pos hc _) := ih
      _ = homeomorph c hc * homeomorph (c ^ (-(n : ℤ) - 1)) (zpow_pos hc _) := by
        rw [← homeomorph_mul]
        congr 1
        simpa only [zpow_one, show (1 : ℤ) + (-(n : ℤ) - 1) = -(n : ℤ) by omega]
          using zpow_add₀ hc.ne' (1 : ℤ) (-(n : ℤ) - 1)

@[simp] theorem action_zero (c : ℝ) (hc : 0 < c) :
    action c hc ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  simp [action]

@[simp] theorem action_top (c : ℝ) (hc : 0 < c) :
    action c hc ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ := by
  apply Subtype.ext
  simp [action, hc.ne']

/-- The actual interval map from the marker theorem. -/
noncomputable def f : I ≃ₜ I := homeomorph 2 (by norm_num)

@[simp] theorem f_coe (u : I) : (f u : ℝ) = rationalIntervalMap u := by
  change 2 * (u : ℝ) / (1 - u + 2 * u) = 2 * (u : ℝ) / (1 + u)
  congr 1 <;> ring

/-- Equality of the original closed absolute-error domain and the compact-selector domain. -/
theorem closedPseudoOrbit_iff (δ : ℝ) (x : ℤ → I) :
    CompactSelector.ClosedPseudoOrbit f δ x ↔ ClosedRationalPseudoOrbit δ x := by
  simp only [CompactSelector.ClosedPseudoOrbit, CompactSelector.linkError,
    ClosedRationalPseudoOrbit, Subtype.dist_eq, Real.dist_eq, f_coe]
  simp only [abs_sub_comm]

@[simp] theorem f_zpow (k : ℤ) : f ^ k = homeomorph ((2 : ℝ) ^ k) (by positivity) :=
  homeomorph_zpow 2 (by norm_num) k

/-- At the negative tail every non-top point tends to the lower endpoint. -/
theorem orbit_neg_tendsto (u : I) (hu : (u : ℝ) < 1) :
    Tendsto (fun n : ℕ => ((f ^ (-(n : ℤ))) u : ℝ)) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h := (ht.mul_const (u : ℝ)).div
    (tendsto_const_nhds.add (ht.mul_const (u : ℝ)))
    (show 1 - (u : ℝ) + 0 * u ≠ 0 by linarith)
  convert h using 1
  · funext n
    rw [f_zpow]
    change (2 : ℝ) ^ (-(n : ℤ)) * u / (1 - (u : ℝ) + (2 : ℝ) ^ (-(n : ℤ)) * u) =
      (1 / 2 : ℝ) ^ n * u / (1 - (u : ℝ) + (1 / 2 : ℝ) ^ n * u)
    simp only [zpow_neg, zpow_natCast]
    rw [← inv_pow]
    norm_num
  · simp

/-- At the positive tail every nonzero point tends to the upper endpoint. -/
theorem orbit_pos_tendsto (u : I) (hu : 0 < (u : ℝ)) :
    Tendsto (fun n : ℕ => ((f ^ (n : ℤ)) u : ℝ)) atTop (𝓝 1) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h := (tendsto_const_nhds (x := (u : ℝ))).div
    ((ht.const_mul (1 - (u : ℝ))).add_const (u : ℝ))
    (show (1 - (u : ℝ)) * 0 + u ≠ 0 by simpa using hu.ne')
  convert h using 1
  · funext n
    rw [f_zpow]
    change (2 : ℝ) ^ (n : ℤ) * u / (1 - (u : ℝ) + (2 : ℝ) ^ (n : ℤ) * u) =
      (u : ℝ) / ((1 - (u : ℝ)) * (1 / 2 : ℝ) ^ n + u)
    simp only [zpow_natCast]
    have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
    have hinv : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
    rw [hinv]
    have hd : 0 < (1 - (u : ℝ)) * ((2 : ℝ) ^ n)⁻¹ + u :=
      add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr u.property.2)
        (inv_nonneg.mpr (pow_nonneg (by norm_num) n))) hu
    apply (div_eq_div_iff (denominator_pos (by positivity) u).ne'
      hd.ne').mpr
    field_simp
    <;> ring
  · simp [hu.ne']

end D5.S1.Dynamics.Shadowing.RationalInterval
