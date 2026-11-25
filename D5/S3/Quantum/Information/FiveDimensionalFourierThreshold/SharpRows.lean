/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Row residuals, exact heavy-row posterior bounds and weighted energy data for the sharp Fourier score. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.CriticalSign
import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierGeometry
import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpParity

/-! Row-residual and centered posterior bounds for the sharp five-dimensional score. -/

open InnerProductSpace QuantumPhaseEstimationGeneral
open D5.S3.Constants.PentagonCosines
open scoped BigOperators ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

theorem sum_univ_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, add_assoc]

def measuredAmplitude (x : CoordinateFive) : FiveRow → ℂ :=
  Sum.elim (fun i => ⟪coordinateBasisFive i, x⟫_ℂ)
    (fun i => ⟪fourierBasisFive i, x⟫_ℂ)

theorem fiveLaw_eq_amplitude (x : CoordinateFive) (i : FiveRow) :
    fiveLaw x i = ‖measuredAmplitude x i‖ ^ 2 := by cases i <;> rfl

def majorityAmplitude (s : Finset FiveRow) (x y : CoordinateFive) (i : FiveRow) : ℂ :=
  if i ∈ s then measuredAmplitude x i else measuredAmplitude y i

def minorityAmplitude (s : Finset FiveRow) (x y : CoordinateFive) (i : FiveRow) : ℂ :=
  if i ∈ s then measuredAmplitude y i else measuredAmplitude x i

/-- The sign from the pair of projections, after putting the majority amplitude first. -/
def rowPhase (s : Finset FiveRow) (i : FiveRow) : ℂ :=
  match i with
  | .inl j => if Sum.inl j ∈ s then 1 else -1
  | .inr j => if Sum.inr j ∈ s then -1 else 1

def rowEnergy (s : Finset FiveRow) (x y : CoordinateFive) (i : FiveRow) : ℝ :=
  ‖(sharpAlpha : ℂ) * majorityAmplitude s x y i -
    rowPhase s i * (sharpBeta : ℂ) * minorityAmplitude s x y i‖ ^ 2

private theorem norm_rowPhase (s : Finset FiveRow) (i : FiveRow) : ‖rowPhase s i‖ = 1 := by
  cases i with
  | inl j => by_cases h : Sum.inl j ∈ s <;> simp [rowPhase, h]
  | inr j => by_cases h : Sum.inr j ∈ s <;> simp [rowPhase, h]

def rowResidual (p q : ℝ) : ℝ := ((1 - sharpC) * p - (1 + sharpC) * q) ^ 2 / (p + q)

private theorem scoreTerm_expand (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    scoreTerm p q =
      2 * sharpC * (p - q) - sharpC ^ 2 * (p + q) + rowResidual p q := by
  by_cases hw : p + q = 0
  · have hp₀ : p = 0 := by linarith
    have hq₀ : q = 0 := by linarith
    simp [scoreTerm, rowResidual, hp₀, hq₀]
  · unfold scoreTerm rowResidual
    field_simp [hw] <;> ring

def maskDeficit (s : Finset FiveRow) (x y : CoordinateFive) : ℝ :=
  2 * sharpC - (maskMass (fiveLaw x) s - maskMass (fiveLaw y) s)

private theorem score_residual_sum (s : Finset FiveRow)
    (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    fiveScore x y = sharpCutoff - 4 * sharpC * maskDeficit s x y +
      ∑ i, rowResidual (‖majorityAmplitude s x y i‖ ^ 2) (‖minorityAmplitude s x y i‖ ^ 2) := by
  let p := fiveLaw x
  let q := fiveLaw y
  let m (i : FiveRow) := if i ∈ s then p i - q i else q i - p i
  have hrow (i : FiveRow) :
      scoreTerm (p i) (q i) =
        2 * sharpC * m i - sharpC ^ 2 * (p i + q i) +
          rowResidual (‖majorityAmplitude s x y i‖ ^ 2) (‖minorityAmplitude s x y i‖ ^ 2) := by
    by_cases hi : i ∈ s
    · simp only [m, majorityAmplitude, minorityAmplitude, if_pos hi]
      rw [← fiveLaw_eq_amplitude, ← fiveLaw_eq_amplitude]
      exact scoreTerm_expand _ _ (fiveLaw_nonneg x i) (fiveLaw_nonneg y i)
    · simp only [m, majorityAmplitude, minorityAmplitude, if_neg hi]
      rw [← fiveLaw_eq_amplitude, ← fiveLaw_eq_amplitude, add_comm (p i) (q i)]
      rw [← scoreTerm_expand _ _ (fiveLaw_nonneg y i) (fiveLaw_nonneg x i)]
      unfold scoreTerm
      rw [add_comm (p i) (q i)]
      congr 1
      ring
  have hm : ∑ i, m i = 2 * (maskMass p s - maskMass q s) := by
    rw [← Finset.sum_compl_add_sum s m]
    have hin : ∑ i ∈ s, m i = maskMass p s - maskMass q s := by
      unfold maskMass
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i hi => if_pos hi
    have hout : ∑ i ∈ sᶜ, m i = maskMass q sᶜ - maskMass p sᶜ := by
      unfold maskMass
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i hi => if_neg (Finset.mem_compl.mp hi)
    rw [hin, hout]
    have hp := (maskMass_add_compl p s).trans (fiveLaw_sum_unit x hx)
    have hq := (maskMass_add_compl q s).trans (fiveLaw_sum_unit y hy)
    linarith only [hp, hq]
  change ∑ i, scoreTerm (p i) (q i) = _
  rw [sharpCutoff_eq]
  simp_rw [hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm]
  have hp : ∑ i, p i = 2 := fiveLaw_sum_unit x hx
  have hq : ∑ i, q i = 2 := fiveLaw_sum_unit y hy
  rw [Finset.sum_add_distrib, hp, hq]
  unfold maskDeficit
  ring

private theorem amplitude_factor {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 < u ^ 2 + v ^ 2) :
    (sharpAlpha * u + sharpBeta * v) ^ 2 / (u ^ 2 + v ^ 2) =
      1 - sharpC + 2 * sharpC * (v ^ 2 / (u ^ 2 + v ^ 2)) +
        2 * sharpB * (u * v / (u ^ 2 + v ^ 2)) := by
  rw [show (sharpAlpha * u + sharpBeta * v) ^ 2 =
      sharpAlpha ^ 2 * u ^ 2 + sharpBeta ^ 2 * v ^ 2 +
        2 * (sharpAlpha * sharpBeta) * u * v by ring,
    sharp_alpha_sq, sharp_beta_sq, sharp_alpha_mul_beta]
  field_simp [hw.ne'] <;> ring

private theorem factor_le_light (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hvu : v ≤ u) (hw : 0 < u ^ 2 + v ^ 2) :
    (sharpAlpha * u + sharpBeta * v) ^ 2 / (u ^ 2 + v ^ 2) ≤ lightWeight := by
  rw [amplitude_factor hu hv hw]
  have hr : v ^ 2 / (u ^ 2 + v ^ 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ hw).mpr
    have hs := (sq_le_sq₀ hv hu).mpr hvu
    linarith
  have hprod : u * v / (u ^ 2 + v ^ 2) ≤ 1 / 2 :=
    (div_le_iff₀ hw).mpr (by nlinarith only [sq_nonneg (u - v)])
  have h₁ := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * sharpC from mul_nonneg (by norm_num) sharpC_pos.le)
  have h₂ := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 * sharpB by linarith [sharp_b_bounds.1])
  unfold lightWeight
  linarith only [h₁, h₂, sharp_b_bounds.2]

private theorem factor_le_heavy (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 < u ^ 2 + v ^ 2) (hcap : v ^ 2 ≤ 0.3 * (u ^ 2 + v ^ 2)) :
    (sharpAlpha * u + sharpBeta * v) ^ 2 / (u ^ 2 + v ^ 2) ≤ heavyWeight := by
  rw [amplitude_factor hu hv hw]
  let r := v ^ 2 / (u ^ 2 + v ^ 2)
  have hr : r ≤ 0.3 := (div_le_iff₀ hw).mpr hcap
  have hprod_sq : (u * v / (u ^ 2 + v ^ 2)) ^ 2 = r * (1 - r) := by
    dsimp [r]
    field_simp [hw.ne'] <;> ring
  have hprod : u * v / (u ^ 2 + v ^ 2) ≤ 0.45825758 := by
    apply (sq_le_sq₀ (div_nonneg (mul_nonneg hu hv) hw.le) (by norm_num)).mp
    rw [hprod_sq]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ (0.7 : ℝ) - r by linarith)]
  have h₁ := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * sharpC from mul_nonneg (by norm_num) sharpC_pos.le)
  have h₂ := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 * sharpB by linarith [sharp_b_bounds.1])
  change 1 - sharpC + 2 * sharpC * r + 2 * sharpB * (u * v / (u ^ 2 + v ^ 2)) ≤ _
  unfold heavyWeight
  linarith only [h₁, h₂, sharp_c_bounds.1, sharp_b_bounds.2]

/-- A probability-weighted amplitude bound, valid even when the minority component vanishes. -/
private theorem rowResidual_le_energy (u v η : ℂ) (k : ℝ) (hη : ‖η‖ = 1)
    (hw : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2)
    (hk : (sharpAlpha * ‖u‖ + sharpBeta * ‖v‖) ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ k) :
    rowResidual (‖u‖ ^ 2) (‖v‖ ^ 2) ≤
      k * ‖(sharpAlpha : ℂ) * u - η * (sharpBeta : ℂ) * v‖ ^ 2 := by
  let A : ℂ := (sharpAlpha : ℂ) * u
  let B : ℂ := η * (sharpBeta : ℂ) * v
  have hA : ‖A‖ = sharpAlpha * ‖u‖ := by
    simp [A, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ sharpAlpha from Real.sqrt_nonneg _)]
  have hB : ‖B‖ = sharpBeta * ‖v‖ := by
    simp [B, norm_mul, hη, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ sharpBeta from Real.sqrt_nonneg _)]
  have hsq : (‖A‖ - ‖B‖) ^ 2 ≤ ‖A - B‖ ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (‖A‖ - ‖B‖)) (norm_nonneg (A - B))).mpr
      (abs_norm_sub_norm_le A B)
    simpa only [sq_abs] using h
  have he : ((1 - sharpC) * ‖u‖ ^ 2 - (1 + sharpC) * ‖v‖ ^ 2) =
      (‖A‖ + ‖B‖) * (‖A‖ - ‖B‖) := by
    rw [hA, hB]
    calc
      _ = (sharpAlpha * ‖u‖) ^ 2 - (sharpBeta * ‖v‖) ^ 2 := by
        rw [mul_pow, mul_pow, sharp_alpha_sq, sharp_beta_sq]
      _ = _ := by ring
  have hcoef : 0 ≤ (‖A‖ + ‖B‖) ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2) := by positivity
  unfold rowResidual
  rw [he, mul_pow]
  calc
    _ = ((‖A‖ + ‖B‖) ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2)) * (‖A‖ - ‖B‖) ^ 2 := by ring
    _ ≤ _ := mul_le_mul (by simpa only [hA, hB] using hk) hsq (sq_nonneg _)
      (hcoef.trans (by simpa only [hA, hB] using hk))

/-- Convert the leverage estimates for either type of heavy row to its posterior cap. -/
theorem sharp_posterior_cap {u v G e L δ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ 0.075) (hL : 0 ≤ L)
    (hgap : G - e - Real.sqrt (δ * L) ≤ Real.sqrt 0.3 * u - Real.sqrt 0.7 * v)
    (hcase :
      (0.300 ≤ G ∧ e ≤ 0.091 * 0.384 ∧ L ≤ 0.84) ∨
      (0.279 ≤ G ∧ e ≤ 0.091 * 0.357 ∧ L ≤ 0.75)) :
    v ^ 2 < 0.3 * (u ^ 2 + v ^ 2) := by
  have hpositive : 0 < Real.sqrt 0.3 * u - Real.sqrt 0.7 * v := by
    rcases hcase with ⟨hg, he, hl⟩ | ⟨hg, he, hl⟩
    · have hmul := mul_le_mul hδ hl hL (by norm_num : (0 : ℝ) ≤ 0.075)
      have hs : Real.sqrt (δ * L) < 0.251 :=
        (Real.sqrt_lt (mul_nonneg hδ₀ hL) (by norm_num)).mpr (by linarith only [hmul])
      linarith only [hg, he, hs, hgap]
    · have hmul := mul_le_mul hδ hl hL (by norm_num : (0 : ℝ) ≤ 0.075)
      have hs : Real.sqrt (δ * L) < 0.238 :=
        (Real.sqrt_lt (mul_nonneg hδ₀ hL) (by norm_num)).mpr (by linarith only [hmul])
      linarith only [hg, he, hs, hgap]
  have hsq := (sq_lt_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hv)
    (mul_nonneg (Real.sqrt_nonneg _) hu)).mpr (sub_pos.mp hpositive)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.7),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.3)] at hsq
  linarith

/-- The two inverse-gap expressions at the four heavy rows in reflected pairs. -/
private theorem pair_row_leverages :
    ((1 + sharpH) / 4) / (sharpC - sharpH) +
      ((1 - sharpH) / 4) / (sharpC + sharpH) + ((1 - sharpC) / 4) / (2 * sharpC) < 0.962 ∧
    ((1 - sharpH) / 4) / (sharpC - sharpH) +
      ((1 + sharpH) / 4) / (sharpC + sharpH) + ((1 + sharpC) / 4) / (2 * sharpC) < 0.785 := by
  have hc := sharp_c_bounds
  have hh := sharp_h_bounds
  have hg : 0.43531350 ≤ sharpC - sharpH := by linarith only [hc.1, hh.2]
  have hs : 1.48677573 ≤ sharpC + sharpH := by linarith only [hc.1, hh.1]
  have ht : 1.92208926 ≤ 2 * sharpC := by linarith only [hc.1]
  have hg' : 0 < sharpC - sharpH := by linarith only [hg]
  have hs' : 0 < sharpC + sharpH := by linarith only [hs]
  have ht' : 0 < 2 * sharpC := by linarith only [ht]
  have hg₁ : ((1 + sharpH) / 4) / (sharpC - sharpH) ≤ 0.87623 := by
    apply (div_le_iff₀ hg').mpr
    linarith only [hg, hh.2]
  have hg₂ : ((1 - sharpH) / 4) / (sharpC - sharpH) ≤ 0.27238 := by
    apply (div_le_iff₀ hg').mpr
    linarith only [hg, hh.1]
  have hs₁ : ((1 + sharpH) / 4) / (sharpC + sharpH) ≤ 0.25656 := by
    apply (div_le_iff₀ hs').mpr
    linarith only [hs, hh.2]
  have hs₂ : ((1 - sharpH) / 4) / (sharpC + sharpH) ≤ 0.07976 := by
    apply (div_le_iff₀ hs').mpr
    linarith only [hs, hh.1]
  have ht₁ : ((1 + sharpC) / 4) / (2 * sharpC) ≤ 0.25508 := by
    apply (div_le_iff₀ ht').mpr
    linarith only [ht, hc.2]
  have ht₂ : ((1 - sharpC) / 4) / (2 * sharpC) ≤ 0.00507 := by
    apply (div_le_iff₀ ht').mpr
    linarith only [ht, hc.1]
  exact ⟨by linarith only [hg₁, hs₂, ht₂], by linarith only [hg₂, hs₁, ht₁]⟩

private theorem center_row_leverages :
    let w := (7 - Real.sqrt 5) / 11
    (1 - w) / sharpC + ((1 - sharpC) * w / 2) / (2 * sharpC) < 0.595 ∧
    (1 - w) / sharpC + ((1 + sharpC) * w / 2) / (2 * sharpC) < 0.812 := by
  dsimp
  let w := (7 - Real.sqrt 5) / 11
  change (1 - w) / sharpC + ((1 - sharpC) * w / 2) / (2 * sharpC) < 0.595 ∧
    (1 - w) / sharpC + ((1 + sharpC) * w / 2) / (2 * sharpC) < 0.812
  have hw₁ : 0.43308472 ≤ w := by dsimp [w]; linarith only [sharp_sqrt_five_bounds.2]
  have hw₂ : w ≤ 0.43308474 := by dsimp [w]; linarith only [sharp_sqrt_five_bounds.1]
  have hw : 0 ≤ w := by linarith only [hw₁]
  have hc := sharp_c_bounds
  have h₁ : (1 - w) / sharpC ≤ 0.58990 := by
    apply (div_le_iff₀ sharpC_pos).mpr
    linarith only [hw₁, hc.1]
  have h₂ : ((1 - sharpC) * w / 2) / (2 * sharpC) ≤ 0.00439 := by
    apply (div_le_iff₀ (by linarith only [hc.1] : 0 < 2 * sharpC)).mpr
    have h := mul_le_mul (show 1 - sharpC ≤ 0.03895537 by linarith only [hc.1]) hw₂
      hw (by norm_num)
    linarith only [h, hc.1]
  have h₃ : ((1 + sharpC) * w / 2) / (2 * sharpC) ≤ 0.22094 := by
    apply (div_le_iff₀ (by linarith only [hc.1] : 0 < 2 * sharpC)).mpr
    have h := mul_le_mul (show 1 + sharpC ≤ 1.96104465 by linarith only [hc.2]) hw₂
      hw (by norm_num)
    linarith only [h, hc.1]
  exact ⟨by linarith only [h₁, h₂], by linarith only [h₁, h₃]⟩

/-- From aligned row expansions and their two error estimates, obtain the signed amplitude gap. -/
private theorem weighted_row_gap (u u₀ x v v₀ y : ℂ) {a a' L₁ L₂ δ₁ δ₂ : ℝ}
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (ha'₁ : a' ≤ 1)
    (hu : u = (a : ℂ) * u₀ + x) (hv : v = (a' : ℂ) * v₀ + y)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hd₁ : 0 ≤ δ₁) (hd₂ : 0 ≤ δ₂)
    (hx : ‖x‖ ≤ Real.sqrt (L₁ * δ₁)) (hy : ‖y‖ ≤ Real.sqrt (L₂ * δ₂)) :
    Real.sqrt 0.3 * ‖u₀‖ - Real.sqrt 0.7 * ‖v₀‖ -
        (1 - a) * (Real.sqrt 0.3 * ‖u₀‖) -
        Real.sqrt ((δ₁ + δ₂) * (0.3 * L₁ + 0.7 * L₂)) ≤
      Real.sqrt 0.3 * ‖u‖ - Real.sqrt 0.7 * ‖v‖ := by
  have hx' : a * ‖u₀‖ - ‖x‖ ≤ ‖u‖ := by
    have h := norm_sub_norm_le ((a : ℂ) * u₀) (-x)
    simpa only [sub_neg_eq_add, norm_neg, ← hu, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha] using h
  have hy' : ‖v‖ ≤ ‖v₀‖ + ‖y‖ := by
    rw [hv]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha']
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha'₁ (norm_nonneg v₀)
  have hweights :
      Real.sqrt 0.3 * ‖x‖ + Real.sqrt 0.7 * ‖y‖ ≤
        Real.sqrt ((δ₁ + δ₂) * (0.3 * L₁ + 0.7 * L₂)) := by
    refine (add_le_add (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))).trans ?_
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 0.3),
      ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 0.7), ← mul_assoc, ← mul_assoc, mul_comm (δ₁ + δ₂)]
    exact sharp_two_errors (mul_nonneg (by norm_num) hL₁) (mul_nonneg (by norm_num) hL₂) hd₁ hd₂
  have hu' := mul_le_mul_of_nonneg_left hx' (Real.sqrt_nonneg 0.3)
  have hv' := mul_le_mul_of_nonneg_left hy' (Real.sqrt_nonneg 0.7)
  nlinarith only [hu', hv', hweights]

/-- Leverage and reference-margin inputs for either heavy-row type yield its posterior cap. -/
private theorem heavy_posterior_of_aligned_errors (u u₀ x v v₀ y : ℂ)
    {a a' L₁ L₂ δ₁ δ₂ : ℝ}
    (ha : 0.909 ≤ a) (ha' : 0 ≤ a') (ha'₁ : a' ≤ 1)
    (hu : u = (a : ℂ) * u₀ + x) (hv : v = (a' : ℂ) * v₀ + y)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hd₁ : 0 ≤ δ₁) (hd₂ : 0 ≤ δ₂)
    (hδ : δ₁ + δ₂ ≤ 0.075)
    (hx : ‖x‖ ≤ Real.sqrt (L₁ * δ₁)) (hy : ‖y‖ ≤ Real.sqrt (L₂ * δ₂))
    (hrow :
      (0.300 ≤ Real.sqrt 0.3 * ‖u₀‖ - Real.sqrt 0.7 * ‖v₀‖ ∧
        Real.sqrt 0.3 * ‖u₀‖ ≤ 0.384 ∧ L₁ ≤ 0.962 ∧ L₂ ≤ 0.785) ∨
      (0.279 ≤ Real.sqrt 0.3 * ‖u₀‖ - Real.sqrt 0.7 * ‖v₀‖ ∧
        Real.sqrt 0.3 * ‖u₀‖ ≤ 0.357 ∧ L₁ ≤ 0.595 ∧ L₂ ≤ 0.812)) :
    ‖v‖ ^ 2 < 0.3 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hgap := weighted_row_gap u u₀ x v v₀ y (show 0 ≤ a by linarith only [ha]) ha' ha'₁
    hu hv hL₁ hL₂ hd₁ hd₂ hx hy
  have hL : 0 ≤ (0.3 : ℝ) * L₁ + 0.7 * L₂ := by linarith only [hL₁, hL₂]
  refine sharp_posterior_cap (norm_nonneg _) (norm_nonneg _) (add_nonneg hd₁ hd₂) hδ hL hgap ?_
  have hA : 0 ≤ Real.sqrt 0.3 * ‖u₀‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rcases hrow with ⟨hG, hA', hl₁, hl₂⟩ | ⟨hG, hA', hl₁, hl₂⟩
  · exact Or.inl ⟨hG, mul_le_mul (by linarith only [ha]) hA' hA (by norm_num),
      by linarith only [hl₁, hl₂]⟩
  · exact Or.inr ⟨hG, mul_le_mul (by linarith only [ha]) hA' hA (by norm_num),
      by linarith only [hl₁, hl₂]⟩

/-- The mismatch cost can be paid for by the positive odd sector and the even leakage. -/
private theorem overlap_mismatch_bound {a a' U V e δe : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (he : 0 ≤ e) (hδe : 0 ≤ δe)
    (hV' : V ≤ 0.0865) (he' : e ≤ 0.173) (heδ : sharpC * e ≤ δe)
    (ha : 1.9 ≤ a + a')
    (hgap : |a ^ 2 - a' ^ 2| ≤ 4 * Real.sqrt (U * V) + e) :
    2 * sharpD * lightWeight * (a - a') ^ 2 ≤ 0.16 * U + 0.02 * δe := by
  have hsqrt := Real.sq_sqrt (mul_nonneg hU hV)
  have hsq := (sq_le_sq₀ (abs_nonneg (a ^ 2 - a' ^ 2))
    (by positivity : 0 ≤ 4 * Real.sqrt (U * V) + e)).mpr hgap
  rw [sq_abs, show a ^ 2 - a' ^ 2 = (a + a') * (a - a') by ring, mul_pow] at hsq
  have hl : (1.9 : ℝ) ^ 2 * (a - a') ^ 2 ≤ (a + a') ^ 2 * (a - a') ^ 2 :=
    mul_le_mul_of_nonneg_right ((sq_le_sq₀ (by norm_num) (by linarith)).mpr ha) (sq_nonneg _)
  have hk : (4 * Real.sqrt (U * V) + e) ^ 2 ≤ 32 * U * V + 2 * e ^ 2 := by
    nlinarith only [sq_nonneg (4 * Real.sqrt (U * V) - e), hsqrt]
  have hcoef : 2 * sharpD * lightWeight ≤ 0.055 * (1.9 : ℝ) ^ 2 := by
    rw [← sharpB_sq]
    have hb := (sq_le_sq₀ (show 0 ≤ sharpB by linarith [sharp_b_bounds.1])
      (by norm_num : (0 : ℝ) ≤ 0.2764)).mpr (by linarith [sharp_b_bounds.2])
    unfold lightWeight
    linarith only [hb]
  have hUV : U * V ≤ 0.0865 * U := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hV' hU
  have he₂ : e ^ 2 ≤ 0.173 * e := by simpa only [pow_two] using mul_le_mul_of_nonneg_right he' he
  have heC : (0.96104 : ℝ) * e ≤ δe :=
    (mul_le_mul_of_nonneg_right (by linarith [sharp_c_bounds.1]) he).trans heδ
  calc
    _ ≤ (0.055 * (1.9 : ℝ) ^ 2) * (a - a') ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ 0.055 * (32 * U * V + 2 * e ^ 2) := by
      have hbound := (hl.trans hsq).trans hk
      nlinarith only [hbound]
    _ ≤ _ := by linarith only [hUV, he₂, heC, hU, he]

/-- Scalar data supplied by the reflection-even and reflection-odd parts of the centered mask. -/
structure CriticalEnergyData (s : Finset FiveRow) (x y : CoordinateFive) where
  lightRows : Finset FiveRow
  oddX : OddCoordinates
  oddY : OddCoordinates
  evenDeficit : ℝ
  evenLeak : ℝ
  overlapX : ℝ
  overlapY : ℝ
  deficit_split : maskDeficit s x y = evenDeficit + oddDeficit oddX oddY
  even_nonneg : 0 ≤ evenDeficit
  even_leak_nonneg : 0 ≤ evenLeak
  even_leak_budget : sharpC * evenLeak ≤ evenDeficit
  total_leak : 2 * (oddMass (oddSector 1 oddX oddY) + oddMass (oddSector (-1) oddX oddY)) +
    evenLeak ≤ 0.173
  overlap_sum : 1.9 ≤ overlapX + overlapY
  overlap_diff : |overlapX ^ 2 - overlapY ^ 2| ≤
    4 * Real.sqrt (oddMass (oddSector 1 oddX oddY) * oddMass (oddSector (-1) oddX oddY)) + evenLeak
  posterior : ∀ i ∉ lightRows, ‖minorityAmplitude s x y i‖ ^ 2 ≤
    0.3 * (‖majorityAmplitude s x y i‖ ^ 2 + ‖minorityAmplitude s x y i‖ ^ 2)
  energy_split :
    (∑ i, (if i ∈ lightRows then lightWeight else heavyWeight) * rowEnergy s x y i) ≤
      oddWeighted oddX oddY +
        lightWeight * (evenCoefficient * evenDeficit + 2 * sharpD * (overlapX - overlapY) ^ 2)

private theorem critical_energy_upper {s : Finset FiveRow} {x y : CoordinateFive}
    (d : CriticalEnergyData s x y) :
    (∑ i, (if i ∈ d.lightRows then lightWeight else heavyWeight) * rowEnergy s x y i) ≤
      4 * sharpC * maskDeficit s x y := by
  let U := oddMass (oddSector 1 d.oddX d.oddY)
  let V := oddMass (oddSector (-1) d.oddX d.oddY)
  have hU : 0 ≤ U := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hV : 0 ≤ V := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hV' : V ≤ 0.0865 := by
    have he := d.even_leak_nonneg
    have h := d.total_leak
    change 2 * (U + V) + d.evenLeak ≤ 0.173 at h
    linarith
  have he' : d.evenLeak ≤ 0.173 := by
    have h := d.total_leak
    change 2 * (U + V) + d.evenLeak ≤ 0.173 at h
    linarith
  have hm := overlap_mismatch_bound hU hV d.even_leak_nonneg d.even_nonneg hV' he'
    d.even_leak_budget d.overlap_sum d.overlap_diff
  have he := mul_le_mul_of_nonneg_right sharp_even_margin.le d.even_nonneg
  have ho := odd_weighted_coercivity d.oddX d.oddY
  change oddWeighted d.oddX d.oddY + 2 * U + 0.0002 * V ≤ _ at ho
  rw [d.deficit_split]
  calc
    _ ≤ _ := d.energy_split
    _ ≤ _ := by nlinarith only [hm, he, ho, hU, hV]

theorem measuredAmplitude_eq_geometry (x : CoordinateFive) (i : FiveRow) :
    measuredAmplitude x i = geometryAmplitude x i := by
  rw [geometryAmplitude_eq_inner]
  cases i <;> rfl

theorem fiveLaw_unit_phase (x : CoordinateFive) (p : ℂ) (hp : ‖p‖ = 1) :
    fiveLaw (p • x) = fiveLaw x := by
  funext i
  simp only [fiveLaw_eq_amplitude, measuredAmplitude_eq_geometry, geometryAmplitude_eq_inner,
    inner_smul_right, norm_mul, hp, one_mul]

theorem align_inner (v x : CoordinateFive) :
    ∃ p : ℂ, ‖p‖ = 1 ∧ ⟪v, p • x⟫_ℂ = (‖⟪v, x⟫_ℂ‖ : ℂ) := by
  let z := ⟪v, x⟫_ℂ
  by_cases hz : z = 0
  · exact ⟨1, norm_one, by rw [one_smul]; change z = ↑‖z‖; simp [hz]⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hn.le, hn.ne']
  · rw [inner_smul_right]
    change conj z / (‖z‖ : ℂ) * z = _
    rw [div_mul_eq_mul_div₀, mul_comm (conj z), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two, mul_div_cancel_right₀ _ hc]

abbrev criticalBasis := centeredEigenbasis true

def criticalIndex (plus : Bool) : CenteredEigenIndex := some (false, plus)

def criticalGap (plus : Bool) (i : CenteredEigenIndex) : ℝ :=
  if plus then 1 + sharpC - centeredEigenvalue true i
  else centeredEigenvalue true i - (1 - sharpC)

theorem criticalGap_zero (plus : Bool) : criticalGap plus (criticalIndex plus) = 0 := by
  cases plus <;>
    simp [criticalGap, criticalIndex, centeredEigenvalue, principalSign, principalOverlap,
      centeredComplementOverlap] <;> ring

private theorem criticalGap_lower (plus : Bool) (i : CenteredEigenIndex)
    (hi : i ≠ criticalIndex plus) : sharpC - sharpH ≤ criticalGap plus i := by
  have hc := sharp_c_bounds.1
  have hh := sharp_h_bounds.1
  cases i with
  | none =>
    cases plus <;> simp [criticalGap, centeredEigenvalue] <;> linarith only [hh]
  | some i =>
    rcases i with ⟨odd, sign⟩
    cases plus <;> cases odd <;> cases sign <;>
      simp [criticalGap, criticalIndex, centeredEigenvalue, principalSign, principalOverlap,
        centeredComplementOverlap] at hi ⊢ <;> linarith only [hc, hh]

private theorem criticalGap_pos (plus : Bool) (i : CenteredEigenIndex)
    (hi : i ≠ criticalIndex plus) : 0 < criticalGap plus i :=
  (show 0 < sharpC - sharpH by linarith [sharp_c_bounds.1, sharp_h_bounds.2]).trans_le
    (criticalGap_lower plus i hi)

def criticalCoefficient (x : CoordinateFive) (i : CenteredEigenIndex) : ℂ :=
  ⟪criticalBasis i, x⟫_ℂ

def criticalOverlap (plus : Bool) (x : CoordinateFive) : ℝ :=
  ‖criticalCoefficient x (criticalIndex plus)‖

def offReference (plus : Bool) : Finset CenteredEigenIndex :=
  Finset.univ.erase (criticalIndex plus)

def spectralDeficit (plus : Bool) (x : CoordinateFive) : ℝ :=
  ∑ i ∈ offReference plus, criticalGap plus i * ‖criticalCoefficient x i‖ ^ 2

private theorem offReference_ne {plus : Bool} {i : CenteredEigenIndex}
    (hi : i ∈ offReference plus) : i ≠ criticalIndex plus :=
  (Finset.mem_erase.mp hi).1

theorem spectralDeficit_nonneg (plus : Bool) (x : CoordinateFive) :
    0 ≤ spectralDeficit plus x :=
  Finset.sum_nonneg fun i hi =>
    mul_nonneg (criticalGap_pos plus i (offReference_ne hi)).le (sq_nonneg _)

theorem criticalCoefficient_sum (x : CoordinateFive) :
    ∑ i, ‖criticalCoefficient x i‖ ^ 2 = ‖x‖ ^ 2 :=
  criticalBasis.sum_sq_norm_inner_right x

private theorem offReference_mass (plus : Bool) (x : CoordinateFive) (hx : ‖x‖ = 1) :
    (∑ i ∈ offReference plus, ‖criticalCoefficient x i‖ ^ 2) =
      1 - criticalOverlap plus x ^ 2 := by
  have h := Finset.sum_erase_add Finset.univ (fun i => ‖criticalCoefficient x i‖ ^ 2)
    (Finset.mem_univ (criticalIndex plus))
  rw [criticalCoefficient_sum, hx, one_pow] at h
  exact eq_sub_of_add_eq h

private theorem overlap_le_one (plus : Bool) (x : CoordinateFive) (hx : ‖x‖ = 1) :
    criticalOverlap plus x ≤ 1 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  have h := offReference_mass plus x hx
  have hn : 0 ≤ ∑ i ∈ offReference plus, ‖criticalCoefficient x i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  change criticalOverlap plus x ^ 2 ≤ (1 : ℝ) ^ 2
  linarith only [h, hn]

private theorem spectralDeficit_leak (plus : Bool) (x : CoordinateFive) (hx : ‖x‖ = 1) :
    (sharpC - sharpH) * (1 - criticalOverlap plus x ^ 2) ≤ spectralDeficit plus x := by
  rw [← offReference_mass plus x hx, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_right (criticalGap_lower plus i (offReference_ne hi)) (sq_nonneg _)

theorem spectralDeficit_eq_mass (plus : Bool) (x : CoordinateFive) :
    spectralDeficit plus x =
      if plus then (1 + sharpC) * ‖x‖ ^ 2 - maskMass (fiveLaw x) centeredRankFive
      else maskMass (fiveLaw x) centeredRankFive - (1 - sharpC) * ‖x‖ ^ 2 := by
  have h := Finset.sum_erase_add Finset.univ
    (fun i => criticalGap plus i * ‖criticalCoefficient x i‖ ^ 2)
    (Finset.mem_univ (criticalIndex plus))
  have hsum : spectralDeficit plus x = ∑ i, criticalGap plus i * ‖criticalCoefficient x i‖ ^ 2 := by
    simpa only [spectralDeficit, offReference, criticalGap_zero, zero_mul, add_zero] using h
  have hm : maskMass (fiveLaw x) centeredRankFive =
      ∑ i, centeredEigenvalue true i * ‖criticalCoefficient x i‖ ^ 2 :=
    centeredMask_mass_spectral true x
  cases plus <;>
    simp only [hsum, hm, criticalGap, Bool.false_eq_true, if_true, if_false, sub_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, criticalCoefficient_sum]

theorem centered_deficit (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    maskDeficit centeredRankFive x y = spectralDeficit true x + spectralDeficit false y := by
  rw [spectralDeficit_eq_mass true, spectralDeficit_eq_mass false, hx, hy]
  simp only [Bool.false_eq_true, if_true, if_false, one_pow, mul_one, maskDeficit]
  ring

theorem centered_overlap_bounds (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hδ : maskDeficit centeredRankFive x y < 0.075) :
    2 - criticalOverlap true x ^ 2 - criticalOverlap false y ^ 2 < 0.173 ∧
    0.909 ≤ criticalOverlap true x ∧ 0.909 ≤ criticalOverlap false y ∧
    1.9 ≤ criticalOverlap true x + criticalOverlap false y := by
  let a := criticalOverlap true x
  let b := criticalOverlap false y
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have ha₁ : a ≤ 1 := overlap_le_one true x hx
  have hb₁ : b ≤ 1 := overlap_le_one false y hy
  have hδ' := centered_deficit x y hx hy
  have hx' := spectralDeficit_leak true x hx
  have hy' := spectralDeficit_leak false y hy
  have hτ : 2 - a ^ 2 - b ^ 2 < 0.173 := sharp_leakage_bound hδ (by
    change (sharpC - sharpH) * (1 - a ^ 2) ≤ _ at hx'
    change (sharpC - sharpH) * (1 - b ^ 2) ≤ _ at hy'
    nlinarith only [hδ', hx', hy'])
  have ha₂ := (sq_le_sq₀ ha (by norm_num : (0 : ℝ) ≤ 1)).mpr ha₁
  have hb₂ := (sq_le_sq₀ hb (by norm_num : (0 : ℝ) ≤ 1)).mpr hb₁
  have hab : (0.9 : ℝ) ≤ a * b := by
    apply (sq_le_sq₀ (by norm_num) (mul_nonneg ha hb)).mp
    rw [mul_pow]
    nlinarith only [hτ, mul_nonneg (sub_nonneg.mpr ha₂) (sub_nonneg.mpr hb₂)]
  refine ⟨hτ, (sq_le_sq₀ (by norm_num) ha).mp ?_, (sq_le_sq₀ (by norm_num) hb).mp ?_,
    (sq_le_sq₀ (by norm_num) (add_nonneg ha hb)).mp ?_⟩
  · linarith only [hτ, hb₂]
  · linarith only [hτ, ha₂]
  · nlinarith only [hτ, hab]

private def criticalLeverage (plus : Bool) (r : FiveRow) : ℝ :=
  ∑ i ∈ offReference plus, ‖geometryAmplitude (criticalBasis i) r‖ ^ 2 / criticalGap plus i

private theorem criticalLeverage_nonneg (plus : Bool) (r : FiveRow) :
    0 ≤ criticalLeverage plus r :=
  Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (criticalGap_pos plus i
    (offReference_ne hi)).le

private theorem centered_row_expansion (plus : Bool) (x : CoordinateFive) (r : FiveRow)
    (hphase : criticalCoefficient x (criticalIndex plus) = (criticalOverlap plus x : ℂ)) :
    ∃ z : ℂ,
      geometryAmplitude x r = (criticalOverlap plus x : ℂ) *
        geometryAmplitude (criticalBasis (criticalIndex plus)) r + z ∧
      ‖z‖ ≤ Real.sqrt (criticalLeverage plus r * spectralDeficit plus x) := by
  let v := ∑ i ∈ offReference plus, criticalCoefficient x i • criticalBasis i
  have hv : v + criticalCoefficient x (criticalIndex plus) • criticalBasis (criticalIndex plus) =
      x := (Finset.sum_erase_add Finset.univ
    (fun i => criticalCoefficient x i • criticalBasis i)
    (Finset.mem_univ (criticalIndex plus))).trans (criticalBasis.sum_repr' x)
  refine ⟨geometryAmplitude v r, ?_, ?_⟩
  · calc
      geometryAmplitude x r =
          geometryAmplitude (v + criticalCoefficient x (criticalIndex plus) •
            criticalBasis (criticalIndex plus)) r :=
        congrArg (fun w => geometryAmplitude w r) hv.symm
      _ = _ := by
        simp only [hphase, geometryAmplitude_eq_inner, inner_add_right, inner_smul_right]
        rw [add_comm]
  · have he := geometryAmplitude_sq_le_weighted (offReference plus) criticalBasis
      (criticalCoefficient x) (criticalGap plus)
      (fun i hi => criticalGap_pos plus i (offReference_ne hi)) r
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg (criticalLeverage_nonneg plus r)
      (spectralDeficit_nonneg plus x))]
    exact he

def centeredLightRows : Finset FiveRow :=
  ({1, 4} : Finset Idx).disjSum {1, 4}

private theorem centered_heavy_rows (r : FiveRow) (hr : r ∉ centeredLightRows) :
    (∃ j ∈ centeredPair, r = Sum.inl j ∨ r = Sum.inr j) ∨
      r = Sum.inl (0 : Idx) ∨ r = Sum.inr (0 : Idx) := by
  cases r with
  | inl j =>
    fin_cases j
    · exact Or.inr (Or.inl rfl)
    · exact (hr (by decide)).elim
    · exact Or.inl ⟨2, by decide, Or.inl rfl⟩
    · exact Or.inl ⟨3, by decide, Or.inl rfl⟩
    · exact (hr (by decide)).elim
  | inr j =>
    fin_cases j
    · exact Or.inr (Or.inr rfl)
    · exact (hr (by decide)).elim
    · exact Or.inl ⟨2, by decide, Or.inr rfl⟩
    · exact Or.inl ⟨3, by decide, Or.inr rfl⟩
    · exact (hr (by decide)).elim

/-- Squared projections at a heavy row, in the majority orientation of the mask. -/
private theorem centered_pair_row_data (j : Idx) (hj : j ∈ centeredPair) (right : Bool) :
    let r : FiveRow := if right then Sum.inr j else Sum.inl j
    (r ∈ centeredRankFive ↔ right = true) ∧
    (∀ odd plus : Bool, ‖geometryAmplitude (criticalBasis (some (odd, plus))) r‖ ^ 2 =
      (1 + (if plus = right then 1 else -1) * centeredComplementOverlap odd) / 4) ∧
    ‖geometryAmplitude (criticalBasis none) r‖ ^ 2 = 0 := by
  dsimp
  cases right
  · refine ⟨by simp [centeredRankFive, hj], ?_, (centeredRankFive_middle_pair_mass j hj).1⟩
    intro odd plus
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false]
    rw [centeredEigenbasis_some, centeredRankFive_ray_standard_pair_mass _ _ hj]
    cases plus <;> simp [principalSign] <;> ring
  · refine ⟨by simp [centeredRankFive, hj], ?_, (centeredRankFive_middle_pair_mass j hj).2⟩
    intro odd plus
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false]
    rw [centeredEigenbasis_some, centeredRay_fourier_pair_mass _ _ _ hj]
    cases plus <;> simp [principalSign, principalOverlap]

private theorem centered_zero_row_data (left : Bool) :
    let r : FiveRow := if left then Sum.inl 0 else Sum.inr 0
    (r ∈ centeredRankFive ↔ left = true) ∧
    (∀ plus : Bool, ‖geometryAmplitude (criticalBasis (some (false, plus))) r‖ ^ 2 =
      (1 + (if plus = left then 1 else -1) * sharpC) * centeredZeroMass / 2) ∧
    (∀ plus : Bool, ‖geometryAmplitude (criticalBasis (some (true, plus))) r‖ ^ 2 = 0) ∧
    ‖geometryAmplitude (criticalBasis none) r‖ ^ 2 = 1 - centeredZeroMass := by
  have h0 : (0 : Idx) ∉ centeredPair := by decide
  dsimp
  cases left
  · refine ⟨by simp [centeredRankFive, h0], ?_, ?_, centeredRankFive_middle_zero_mass.2⟩
    · intro plus
      simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false]
      rw [centeredEigenbasis_some, (centeredRankFive_ray_zero_mass _).2]
      cases plus <;> simp [principalSign] <;> ring <;> simp
    · intro plus
      simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false]
      rw [centeredEigenbasis_some, (centeredRay_odd_zero true plus).2, norm_zero, zero_pow two_ne_zero]
  · refine ⟨by simp [centeredRankFive, h0], ?_, ?_, centeredRankFive_middle_zero_mass.1⟩
    · intro plus
      simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false]
      rw [centeredEigenbasis_some, (centeredRankFive_ray_zero_mass _).1]
      cases plus <;> simp [principalSign]
    · intro plus
      simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false]
      rw [centeredEigenbasis_some, (centeredRay_odd_zero true plus).1, norm_zero, zero_pow two_ne_zero]

private theorem reference_pair_margin {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu₂ : u ^ 2 = (1 + sharpC) / 4) (hv₂ : v ^ 2 = (1 - sharpC) / 4) :
    0.300 ≤ Real.sqrt 0.3 * u - Real.sqrt 0.7 * v ∧ Real.sqrt 0.3 * u ≤ 0.384 := by
  have h₁ : (Real.sqrt 0.3 * u) ^ 2 = 0.3 * ((1 + sharpC) / 4) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.3), hu₂]
  have h₂ : (Real.sqrt 0.7 * v) ^ 2 = 0.7 * ((1 - sharpC) / 4) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.7), hv₂]
  have ha : 0.383 ≤ Real.sqrt 0.3 * u :=
    (sq_le_sq₀ (by norm_num) (by positivity)).mp (by linarith only [h₁, sharp_c_bounds.1])
  have hb : Real.sqrt 0.7 * v ≤ 0.083 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mp (by linarith only [h₂, sharp_c_bounds.1])
  exact ⟨by linarith only [ha, hb],
    (sq_le_sq₀ (by positivity) (by norm_num)).mp (by linarith only [h₁, sharp_c_bounds.2])⟩

private theorem reference_zero_margin {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu₂ : u ^ 2 = (1 + sharpC) * centeredZeroMass / 2)
    (hv₂ : v ^ 2 = (1 - sharpC) * centeredZeroMass / 2) :
    0.279 ≤ Real.sqrt 0.3 * u - Real.sqrt 0.7 * v ∧ Real.sqrt 0.3 * u ≤ 0.357 := by
  have hw₁ : 0.43308472 ≤ centeredZeroMass := by
    rw [centeredZeroMass_eq]
    linarith only [sharp_sqrt_five_bounds.2]
  have hw₂ : centeredZeroMass ≤ 0.43308474 := by
    rw [centeredZeroMass_eq]
    linarith only [sharp_sqrt_five_bounds.1]
  have hw : 0 ≤ centeredZeroMass := by linarith only [hw₁]
  have ht₁ := mul_le_mul (show (1.96104463 : ℝ) ≤ 1 + sharpC by linarith [sharp_c_bounds.1])
    hw₁ (by norm_num) (by linarith [sharp_c_bounds.1])
  have ht₂ := mul_le_mul (show 1 + sharpC ≤ (1.96104465 : ℝ) by linarith [sharp_c_bounds.2])
    hw₂ hw (by norm_num)
  have ht₃ := mul_le_mul (show 1 - sharpC ≤ (0.03895537 : ℝ) by linarith [sharp_c_bounds.1])
    hw₂ hw (by norm_num)
  have h₁ : (Real.sqrt 0.3 * u) ^ 2 = 0.3 * ((1 + sharpC) * centeredZeroMass / 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.3), hu₂]
  have h₂ : (Real.sqrt 0.7 * v) ^ 2 = 0.7 * ((1 - sharpC) * centeredZeroMass / 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 0.7), hv₂]
  have ha : 0.356 ≤ Real.sqrt 0.3 * u :=
    (sq_le_sq₀ (by norm_num) (by positivity)).mp (by linarith only [h₁, ht₁])
  have hb : Real.sqrt 0.7 * v ≤ 0.077 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mp (by linarith only [h₂, ht₃])
  exact ⟨by linarith only [ha, hb],
    (sq_le_sq₀ (by positivity) (by norm_num)).mp (by linarith only [h₁, ht₂])⟩

private theorem leverage_sum (plus : Bool) (r : FiveRow) :
    criticalLeverage plus r =
      ∑ i, ‖geometryAmplitude (criticalBasis i) r‖ ^ 2 / criticalGap plus i := by
  have h := Finset.sum_erase_add Finset.univ
    (fun i => ‖geometryAmplitude (criticalBasis i) r‖ ^ 2 / criticalGap plus i)
    (Finset.mem_univ (criticalIndex plus))
  simpa only [criticalLeverage, offReference, criticalGap_zero, div_zero, add_zero] using h

theorem criticalGap_even (plus sign : Bool) :
    criticalGap plus (some (false, sign)) = if plus = sign then 0 else 2 * sharpC := by
  cases plus <;> cases sign <;>
    simp [criticalGap, centeredEigenvalue, principalSign, principalOverlap,
      centeredComplementOverlap] <;> ring

private theorem criticalGap_odd (plus sign : Bool) :
    criticalGap plus (some (true, sign)) =
      if plus = sign then sharpC - sharpH else sharpC + sharpH := by
  cases plus <;> cases sign <;>
    simp [criticalGap, centeredEigenvalue, principalSign, principalOverlap,
      centeredComplementOverlap] <;> ring

theorem criticalGap_middle (plus : Bool) : criticalGap plus none = sharpC := by
  cases plus <;> simp [criticalGap, centeredEigenvalue] <;> ring

set_option maxHeartbeats 1000000 in
private theorem centered_pair_leverages (j : Idx) (hj : j ∈ centeredPair) (right : Bool) :
    let r : FiveRow := if right then Sum.inr j else Sum.inl j
    criticalLeverage right r ≤ 0.962 ∧ criticalLeverage (!right) r ≤ 0.785 := by
  obtain ⟨_, hmass, hmiddle⟩ := centered_pair_row_data j hj right
  have h := pair_row_leverages
  cases right <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false,
      Bool.not_false, Bool.not_true] at hmass hmiddle ⊢
  all_goals
    simp only [leverage_sum, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
      hmass, hmiddle, criticalGap_middle, criticalGap_even, criticalGap_odd,
      centeredComplementOverlap, Bool.false_eq_true, Bool.true_eq_false, eq_self,
      ite_true, ite_false, zero_div, div_zero, zero_add, add_zero, neg_one_mul, one_mul,
      ← sub_eq_add_neg]
    constructor <;> linarith only [h.1, h.2]

set_option maxHeartbeats 1000000 in
private theorem centered_zero_leverages (left : Bool) :
    let r : FiveRow := if left then Sum.inl 0 else Sum.inr 0
    criticalLeverage left r ≤ 0.595 ∧ criticalLeverage (!left) r ≤ 0.812 := by
  obtain ⟨_, hmass, hodd, hmiddle⟩ := centered_zero_row_data left
  have h := center_row_leverages
  dsimp only at h
  cases left <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, ite_true, ite_false,
      Bool.not_false, Bool.not_true] at hmass hodd hmiddle ⊢
  all_goals
    simp only [leverage_sum, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
      hmass, hodd, hmiddle, criticalGap_middle, criticalGap_even, criticalGap_odd,
      centeredZeroMass_eq, Bool.false_eq_true, Bool.true_eq_false, eq_self,
      ite_true, ite_false, zero_div, div_zero, zero_add, add_zero, neg_one_mul, one_mul,
      ← sub_eq_add_neg]
    constructor <;> linarith only [h.1, h.2]

theorem centered_heavy_posterior (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hδ : maskDeficit centeredRankFive x y < 0.075)
    (hpx : criticalCoefficient x (criticalIndex true) = (criticalOverlap true x : ℂ))
    (hpy : criticalCoefficient y (criticalIndex false) = (criticalOverlap false y : ℂ))
    (r : FiveRow) (hr : r ∉ centeredLightRows) :
    ‖minorityAmplitude centeredRankFive x y r‖ ^ 2 ≤
      0.3 * (‖majorityAmplitude centeredRankFive x y r‖ ^ 2 +
        ‖minorityAmplitude centeredRankFive x y r‖ ^ 2) := by
  obtain ⟨_, hax, hay, _⟩ := centered_overlap_bounds x y hx hy hδ
  have hbudget : spectralDeficit true x + spectralDeficit false y ≤ 0.075 :=
    (centered_deficit x y hx hy) ▸ hδ.le
  obtain ⟨dx, hdx, hex⟩ := centered_row_expansion true x r hpx
  obtain ⟨dy, hdy, hey⟩ := centered_row_expansion false y r hpy
  let A (p : Bool) := geometryAmplitude (criticalBasis (criticalIndex p)) r
  let profile (p : Bool) : Prop :=
    (0.300 ≤ Real.sqrt 0.3 * ‖A p‖ - Real.sqrt 0.7 * ‖A (!p)‖ ∧
      Real.sqrt 0.3 * ‖A p‖ ≤ 0.384 ∧
      criticalLeverage p r ≤ 0.962 ∧ criticalLeverage (!p) r ≤ 0.785) ∨
    (0.279 ≤ Real.sqrt 0.3 * ‖A p‖ - Real.sqrt 0.7 * ‖A (!p)‖ ∧
      Real.sqrt 0.3 * ‖A p‖ ≤ 0.357 ∧
      criticalLeverage p r ≤ 0.595 ∧ criticalLeverage (!p) r ≤ 0.812)
  have hprofile : ∃ p : Bool, (r ∈ centeredRankFive ↔ p = true) ∧ profile p := by
    have hp (j : Idx) (hj : j ∈ centeredPair) (right : Bool)
        (he : r = if right then Sum.inr j else Sum.inl j) :
        (r ∈ centeredRankFive ↔ right = true) ∧ profile right := by
      obtain ⟨hm, hmasses, _⟩ := centered_pair_row_data j hj right
      have hL := centered_pair_leverages j hj right
      refine ⟨by simpa only [he] using hm, Or.inl ?_⟩
      have hmaj : ‖A right‖ ^ 2 = (1 + sharpC) / 4 := by
        simpa [A, criticalIndex, he, principalSign, centeredComplementOverlap] using
          hmasses false right
      have hmin : ‖A (!right)‖ ^ 2 = (1 - sharpC) / 4 := by
        cases right
        · simpa [A, criticalIndex, he, centeredComplementOverlap, sub_eq_add_neg] using
            hmasses false true
        · simpa [A, criticalIndex, he, centeredComplementOverlap, sub_eq_add_neg] using
            hmasses false false
      have hM := reference_pair_margin (norm_nonneg _) (norm_nonneg _) hmaj hmin
      exact ⟨hM.1, hM.2, by simpa only [he] using hL.1, by simpa only [he] using hL.2⟩
    have hz (left : Bool) (he : r = if left then Sum.inl 0 else Sum.inr 0) :
        (r ∈ centeredRankFive ↔ left = true) ∧ profile left := by
      obtain ⟨hm, hmasses, _, _⟩ := centered_zero_row_data left
      have hL := centered_zero_leverages left
      refine ⟨by simpa only [he] using hm, Or.inr ?_⟩
      have hmaj : ‖A left‖ ^ 2 = (1 + sharpC) * centeredZeroMass / 2 := by
        simpa [A, criticalIndex, he, principalSign] using hmasses left
      have hmin : ‖A (!left)‖ ^ 2 = (1 - sharpC) * centeredZeroMass / 2 := by
        cases left
        · simpa [A, criticalIndex, he, sub_eq_add_neg] using hmasses true
        · simpa [A, criticalIndex, he, sub_eq_add_neg] using hmasses false
      have hM := reference_zero_margin (norm_nonneg _) (norm_nonneg _) hmaj hmin
      exact ⟨hM.1, hM.2, by simpa only [he] using hL.1, by simpa only [he] using hL.2⟩
    rcases centered_heavy_rows r hr with ⟨j, hj, hj' | hj'⟩ | hj' | hj'
    · exact ⟨false, hp j hj false hj'⟩
    · exact ⟨true, hp j hj true hj'⟩
    · exact ⟨true, hz true hj'⟩
    · exact ⟨false, hz false hj'⟩
  obtain ⟨p, hp, hp'⟩ := hprofile
  cases p
  · have hn : r ∉ centeredRankFive := fun h => Bool.false_ne_true (hp.mp h)
    simp only [majorityAmplitude, minorityAmplitude, if_neg hn, measuredAmplitude_eq_geometry]
    exact (heavy_posterior_of_aligned_errors _ _ dy _ _ dx hay (norm_nonneg _)
      (overlap_le_one true x hx) hdy hdx (criticalLeverage_nonneg false r)
      (criticalLeverage_nonneg true r) (spectralDeficit_nonneg false y)
      (spectralDeficit_nonneg true x) (by rwa [add_comm]) hey hex hp').le
  · have hm := hp.mpr rfl
    simp only [majorityAmplitude, minorityAmplitude, if_pos hm, measuredAmplitude_eq_geometry]
    exact (heavy_posterior_of_aligned_errors _ _ dx _ _ dy hax (norm_nonneg _)
      (overlap_le_one false y hy) hdx hdy (criticalLeverage_nonneg true r)
      (criticalLeverage_nonneg false r) (spectralDeficit_nonneg true x)
      (spectralDeficit_nonneg false y) hbudget hex hey hp').le

theorem score_le_of_energy_data (s : Finset FiveRow) (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hs : SignCompatible (fiveLaw x) (fiveLaw y) s) (d : CriticalEnergyData s x y) :
    fiveScore x y ≤ sharpCutoff := by
  classical
  rw [score_residual_sum s x y hx hy]
  have hbound :
      (∑ i, rowResidual (‖majorityAmplitude s x y i‖ ^ 2) (‖minorityAmplitude s x y i‖ ^ 2)) ≤
        4 * sharpC * maskDeficit s x y := by
    refine (Finset.sum_le_sum (s := Finset.univ) (g := fun i =>
      (if i ∈ d.lightRows then lightWeight else heavyWeight) * rowEnergy s x y i) ?_).trans
        (critical_energy_upper d)
    intro i _
    let u := majorityAmplitude s x y i
    let v := minorityAmplitude s x y i
    change rowResidual (‖u‖ ^ 2) (‖v‖ ^ 2) ≤
      (if i ∈ d.lightRows then lightWeight else heavyWeight) *
        ‖(sharpAlpha : ℂ) * u - rowPhase s i * (sharpBeta : ℂ) * v‖ ^ 2
    by_cases hw : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2
    swap
    · have hu₂ : ‖u‖ ^ 2 = 0 := le_antisymm
        (by linarith only [le_of_not_gt hw, sq_nonneg ‖v‖]) (sq_nonneg _)
      have hv₂ : ‖v‖ ^ 2 = 0 := le_antisymm
        (by linarith only [le_of_not_gt hw, sq_nonneg ‖u‖]) (sq_nonneg _)
      have hu : u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hu₂)
      have hv : v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hv₂)
      simp [rowResidual, hu, hv]
    apply rowResidual_le_energy u v (rowPhase s i) _ (norm_rowPhase s i) hw
    by_cases hi : i ∈ d.lightRows
    · rw [if_pos hi]
      have hvu : ‖v‖ ≤ ‖u‖ := by
        apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        by_cases his : i ∈ s
        · simpa [u, v, majorityAmplitude, minorityAmplitude, his, ← fiveLaw_eq_amplitude] using hs.1 i his
        · simpa [u, v, majorityAmplitude, minorityAmplitude, his, ← fiveLaw_eq_amplitude] using hs.2 i his
      exact factor_le_light _ _ (norm_nonneg _) (norm_nonneg _) hvu hw
    · rw [if_neg hi]
      exact factor_le_heavy _ _ (norm_nonneg _) (norm_nonneg _) hw (d.posterior i hi)
  linarith only [hbound]

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
