/- GID: D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A logarithmic square tail enlarges the critical missing-window exponent. -/

import D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow

/-! Critical missing windows with a logarithmic gain in the waiting exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators NNReal

attribute [local instance] Classical.propDecidable

namespace D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow

open OrdinateCounting (Spectrum)
open SpectrumPhaseCutoff (mass sine)
open SpectrumCriticalMissingWindow (HasLogSquaredMass log_shifted_cutoff shifted_cutoff_le
  eventual_mass_margin eventual_mesh_cost grid_count_le missing_window_of_cutoff)

/-- A uniform square-weight bound of order `log X / X` over every finite upper cutoff. -/
def HasLogarithmicSquareTail (S : Spectrum) (w : S.index → ℝ) : Prop := by
  classical
  exact ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ T : ℝ, X ≤ T →
    ∑ j ∈ S.cut T \ S.cut X, w j ^ 2 ≤ C * Real.log X / X

private theorem eventual_logarithmic_grid_bound {r β c : ℝ}
    (hr : 0 < r) (hβ : 0 < β) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop,
      let E := c * T ^ β * Real.log T
      (⌊(Real.exp E / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1 < Real.exp (2 * E) := by
  let B := 1 / r + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hgrow := ((tendsto_rpow_atTop hβ).const_mul_atTop hc).eventually_gt_atTop
    (2 + Real.log B)
  filter_upwards [hgrow, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (1 : ℝ)] with T hg hlog hT
  let E := c * T ^ β * Real.log T
  change (⌊(Real.exp E / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1 < _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoly : T ^ 2 / r + 1 ≤ B * T ^ 2 := by
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT.le
    dsimp [B]
    linarith only [hT2, show (1 / r + 1) * T ^ 2 = T ^ 2 / r + T ^ 2 by ring]
  have hlogBudget : 2 * Real.log T + Real.log B < E := by
    change 2 + Real.log B < c * T ^ β at hg
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by dsimp [B]; linarith [div_pos one_pos hr])
    have hcost := mul_le_mul_of_nonneg_left hlog hlogB
    have hstrict := mul_lt_mul_of_pos_right hg (zero_lt_one.trans_le hlog)
    dsimp [E]
    nlinarith only [hcost, hstrict]
  have hpolyExp : B * T ^ 2 = Real.exp (2 * Real.log T + Real.log B) := by
    rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log hB,
      Real.exp_log (zero_lt_one.trans hT)]
    ring
  calc
    _ ≤ Real.exp E * (T ^ 2 / r + 1) := grid_count_le (Real.one_le_exp_iff.mpr hE) hr
    _ ≤ Real.exp E * (B * T ^ 2) := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ < Real.exp E * Real.exp E := by
      rw [hpolyExp]
      exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlogBudget) (Real.exp_pos _)
    _ = Real.exp (2 * E) := by rw [← Real.exp_add, two_mul]

/-- A logarithmic square-tail bound gives a strictly positive logarithmic gain in the
waiting exponent at the same critical mass fraction and signed logarithmic margin. -/
theorem eventual_logarithmic_missing_window (S : Spectrum) (w : S.index → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hli : LinearIndependent ℚ S.gamma)
    (hmass : HasLogSquaredMass S w) (htail : HasLogarithmicSquareTail S w)
    {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) (hβ₁ : β < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ A : ℝ, ∃ a > A, ∀ u ∈ Icc a (a + Real.exp (c * T ^ β * Real.log T)),
        sine S w T (u / r) < β ^ 2 * mass S w T - Real.log T := by
  classical
  obtain ⟨a, Cmass, ha, hCmass, hmass⟩ := hmass
  obtain ⟨C, hC, htail⟩ := htail
  obtain ⟨K, hK, hmargin⟩ := eventual_mass_margin ha hCmass hβ hmass
  let D := C * β * Real.exp K
  have hD : 0 < D := by dsimp [D]; positivity
  let c := 1 / (4 * D)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  let X (T : ℝ) := Real.exp (-K) * T ^ β
  have hX := (tendsto_rpow_atTop hβ).const_mul_atTop (Real.exp_pos (-K))
  filter_upwards [hmargin, eventual_mesh_cost ha hCmass hmass,
    eventual_logarithmic_grid_bound hr hβ hc, hX.eventually htail,
    eventually_gt_atTop (1 : ℝ)] with T hmarginT hmeshT hgridT htailT hT
  have hTpos := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hpowpos := Real.rpow_pos_of_pos hTpos β
  have hXT : X T ≤ T := shifted_cutoff_le hK.le hT.le hβ₁.le
  have hlogX : Real.log (X T) = β * Real.log T - K := log_shifted_cutoff hTpos K β
  let E := c * T ^ β * Real.log T
  let V := ∑ j ∈ S.cut T \ S.cut (X T), w j ^ 2
  have hV : V ≤ D * Real.log T / T ^ β := by
    calc
      V ≤ C * Real.log (X T) / X T := htailT T hXT
      _ ≤ C * (β * Real.log T) / X T := by
        gcongr
        linarith only [hlogX, hK]
      _ = _ := by
        dsimp only [X, D]
        rw [Real.exp_neg, div_mul_eq_div_div, div_inv_eq_mul]
        ring
  have hbudget : V = 0 ∨
      ((⌊(Real.exp E / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1) *
        Real.exp (-Real.log T ^ 2 / (2 * V)) < 1 := by
    by_cases hz : V = 0
    · exact Or.inl hz
    · right
      have hVpos : 0 < V :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (w j)) (Ne.symm hz)
      have hVmul := (le_div_iff₀ hpowpos).mp hV
      have hrate : T ^ β * Real.log T / (2 * D) ≤ Real.log T ^ 2 / (2 * V) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * D)
          (by positivity : 0 < 2 * V)).mpr
        convert mul_le_mul_of_nonneg_right hVmul (by positivity : 0 ≤ 2 * Real.log T)
          using 1 <;> ring
      have hTwoE : 2 * E = T ^ β * Real.log T / (2 * D) := by
        dsimp only [E, c]
        ring
      calc
        _ < Real.exp (2 * E) * Real.exp (-Real.log T ^ 2 / (2 * V)) :=
          mul_lt_mul_of_pos_right hgridT (Real.exp_pos _)
        _ ≤ Real.exp (2 * E) * Real.exp (-(2 * E)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply Real.exp_le_exp.mpr
          rw [hTwoE, neg_div]
          exact neg_le_neg hrate
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact missing_window_of_cutoff hw hli hT hr hXT hmarginT hmeshT hbudget

#print axioms eventual_logarithmic_missing_window

end D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow
