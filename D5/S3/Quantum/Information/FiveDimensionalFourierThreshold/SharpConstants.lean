/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact radicals and rational brackets certify the scalar bounds for the sharp five-dimensional score. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveThreshold

/-! Exact radical and rational bounds for the sharp five-dimensional score. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

def sharpC : ℝ := Real.sqrt ((7 + Real.sqrt 5) / 10)
def sharpH : ℝ := Real.sqrt ((5 - Real.sqrt 5) / 10)
def sharpSigma : ℝ := Real.sqrt ((5 + Real.sqrt 5) / 10)
def sharpD : ℝ := (3 - Real.sqrt 5) / 10
def sharpB : ℝ := Real.sqrt sharpD
def sharpAlpha : ℝ := Real.sqrt (1 - sharpC)
def sharpBeta : ℝ := Real.sqrt (1 + sharpC)
def sharpCutoff : ℝ := (14 + 2 * Real.sqrt 5) / 5
def lightWeight : ℝ := 1.2764
def heavyWeight : ℝ := 0.8690
def evenCoefficient : ℝ := 2 * sharpC + 2 * sharpB * (sharpB + 1) / sharpC

theorem sharp_sqrt_bracket {x l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (h₁ : l ^ 2 < x) (h₂ : x < u ^ 2) : l < Real.sqrt x ∧ Real.sqrt x < u :=
  ⟨(Real.lt_sqrt hl).mpr h₁, (Real.sqrt_lt (by nlinarith only [h₁, sq_nonneg l]) hu).mpr h₂⟩

theorem sharp_sqrt_five_bounds : (2.2360679774 : ℝ) < Real.sqrt 5 ∧
    Real.sqrt 5 < 2.2360679776 :=
  sharp_sqrt_bracket (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sharp_c_bounds : 0.96104463 < sharpC ∧ sharpC < 0.96104465 := by
  obtain ⟨hl, hu⟩ := sharp_sqrt_five_bounds
  unfold sharpC
  exact sharp_sqrt_bracket (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem sharp_h_bounds : 0.52573110 < sharpH ∧ sharpH < 0.52573113 := by
  obtain ⟨hl, hu⟩ := sharp_sqrt_five_bounds
  unfold sharpH
  exact sharp_sqrt_bracket (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem sharp_sigma_bounds : 0.85065080 < sharpSigma ∧ sharpSigma < 0.85065082 := by
  obtain ⟨hl, hu⟩ := sharp_sqrt_five_bounds
  unfold sharpSigma
  exact sharp_sqrt_bracket (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem sharp_b_bounds : 0.27639319 < sharpB ∧ sharpB < 0.27639322 := by
  obtain ⟨hl, hu⟩ := sharp_sqrt_five_bounds
  unfold sharpB sharpD
  exact sharp_sqrt_bracket (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem sharp_alpha_bounds : 0.1973710 < sharpAlpha ∧ sharpAlpha < 0.1973713 := by
  obtain ⟨hl, hu⟩ := sharp_c_bounds
  unfold sharpAlpha
  exact sharp_sqrt_bracket (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem sharp_beta_bounds : 1.4003730 < sharpBeta ∧ sharpBeta < 1.4003731 := by
  obtain ⟨hl, hu⟩ := sharp_c_bounds
  unfold sharpBeta
  exact sharp_sqrt_bracket (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem sharpC_pos : 0 < sharpC := by linarith [sharp_c_bounds.1]

theorem sharpC_lt_one : sharpC < 1 := by linarith [sharp_c_bounds.2]

theorem sharpC_sq : sharpC ^ 2 = (7 + Real.sqrt 5) / 10 :=
  Real.sq_sqrt (by positivity)

theorem sharpD_eq : sharpD = 1 - sharpC ^ 2 := by
  rw [sharpC_sq]
  unfold sharpD
  ring

theorem sharpB_sq : sharpB ^ 2 = sharpD := by
  apply Real.sq_sqrt
  rw [sharpD_eq]
  nlinarith only [sharpC_pos, sharpC_lt_one, mul_nonneg sharpC_pos.le (sub_nonneg.mpr sharpC_lt_one.le)]

theorem sharpCutoff_eq : sharpCutoff = 4 * sharpC ^ 2 := by
  rw [sharpC_sq]
  unfold sharpCutoff
  ring

theorem sharp_alpha_sq : sharpAlpha ^ 2 = 1 - sharpC :=
  Real.sq_sqrt (sub_nonneg.mpr sharpC_lt_one.le)

theorem sharp_beta_sq : sharpBeta ^ 2 = 1 + sharpC :=
  Real.sq_sqrt (add_nonneg zero_le_one sharpC_pos.le)

theorem sharp_alpha_mul_beta : sharpAlpha * sharpBeta = sharpB := by
  have ha : 0 ≤ sharpAlpha := Real.sqrt_nonneg _
  have hb : 0 ≤ sharpBeta := Real.sqrt_nonneg _
  apply (sq_eq_sq₀ (mul_nonneg ha hb) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, sharp_alpha_sq, sharp_beta_sq, show Real.sqrt sharpD ^ 2 = sharpD from sharpB_sq,
    sharpD_eq]
  ring

theorem sharp_h_sigma_sq : sharpH ^ 2 + sharpSigma ^ 2 = 1 := by
  have hh : 0 ≤ (5 - Real.sqrt 5) / 10 := by linarith [sharp_sqrt_five_bounds.2]
  have hs : 0 ≤ (5 + Real.sqrt 5) / 10 := by positivity
  unfold sharpH sharpSigma
  rw [Real.sq_sqrt hh, Real.sq_sqrt hs]
  ring

theorem sharp_budget_lt : 2 * sharpC * (1 - sharpC) < 0.075 := by
  have h₁ : sharpC ≤ 0.96104465 := sharp_c_bounds.2.le
  have h₂ : 1 - sharpC ≤ 0.03895537 := by linarith [sharp_c_bounds.1]
  calc
    _ ≤ 2 * (0.96104465 : ℝ) * 0.03895537 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by norm_num)) h₂
        (sub_nonneg.mpr sharpC_lt_one.le) (by norm_num)
    _ < _ := by norm_num

theorem sharp_leakage_bound {δ τ : ℝ} (hδ : δ < 0.075)
    (hτ : (sharpC - sharpH) * τ ≤ δ) : τ < 0.173 := by
  have hg : (0.43530 : ℝ) < sharpC - sharpH :=
    by linarith [sharp_c_bounds.1, sharp_h_bounds.2]
  by_contra! h
  have hprod := mul_le_mul (show (0.43530 : ℝ) ≤ sharpC - sharpH from hg.le) h
    (by norm_num) (by linarith)
  linarith

theorem sharp_even_margin : lightWeight * evenCoefficient + 0.02 < 4 * sharpC := by
  have hb : sharpB ≤ 0.2764 := by linarith [sharp_b_bounds.2]
  have hprod : 2 * sharpB * (sharpB + 1) ≤ 2 * (0.2764 : ℝ) * (0.2764 + 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) (by linarith)
      (by linarith [sharp_b_bounds.1]) (by norm_num)
  have hu : 2 * sharpB * (sharpB + 1) / sharpC ≤
      2 * (0.2764 : ℝ) * (0.2764 + 1) / 0.96104 := by
    apply (div_le_iff₀ sharpC_pos).mpr
    have hc : (0.96104 : ℝ) ≤ sharpC := by linarith [sharp_c_bounds.1]
    have h := mul_le_mul_of_nonneg_left hc
      (show (0 : ℝ) ≤ 2 * 0.2764 * (0.2764 + 1) / 0.96104 by norm_num)
    linarith
  unfold lightWeight evenCoefficient
  linarith [sharp_c_bounds.1, sharp_c_bounds.2]

/-- Two-term weighted Cauchy–Schwarz in the form used for joint deficits. -/
theorem sharp_two_errors {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (a * u) + Real.sqrt (b * v) ≤ Real.sqrt ((a + b) * (u + v)) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul hb]
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  have he := sq_nonneg (Real.sqrt a * Real.sqrt v - Real.sqrt b * Real.sqrt u)
  have hex :
      (Real.sqrt a * Real.sqrt u + Real.sqrt b * Real.sqrt v) ^ 2 +
        (Real.sqrt a * Real.sqrt v - Real.sqrt b * Real.sqrt u) ^ 2 =
      (Real.sqrt a ^ 2 + Real.sqrt b ^ 2) * (Real.sqrt u ^ 2 + Real.sqrt v ^ 2) := by ring
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hu, Real.sq_sqrt hv] at hex
  linarith

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
