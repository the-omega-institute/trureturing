/- GID: D5/S3/Analytic/Oscillation/MontgomeryCountSharpness
   generality: I
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryCountSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The count-discrepancy upper coefficient is attained along logarithmic phase bands. -/

import D5.S3.Analytic.Oscillation.MontgomeryCountUpper
import D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
import D5.S3.Fourier.Concentration.CauchyPairEnergy

/-! A commensurate spectrum attains the leading counting bound in a fixed logarithmic band. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomeryCountSharpness

open OrdinateCounting (Spectrum CountAsymptotic)
open SpectrumPhaseCutoff (mass sine mem_cut)
open SmoothedSpectrumCounting.CutDensity (countMain)
open MontgomeryCountUpper (count_asymptotic_of_bounded_discrepancy pairSum
  pairSum_le_of_bounded_discrepancy)
open MontgomeryWindow (pairCos)
open D5.S3.Fourier.Concentration.CauchyPairEnergy (lorentz_pair_lower_bound)

private abbrev c : ℝ := 1 / (2 * Real.pi)
private abbrev threshold : ℝ := 2 * Real.pi * c ^ 2

private theorem lower_of_alignment (S : Spectrum) {Y R t : ℝ} (hR : 0 ≤ R)
    (halign : ∀ j ∈ S.cut Y, Real.sin (S.gamma j * t) = 1) :
    (2 * Real.pi) / (Y + 2 * R) *
      ((Real.pi⁻¹ * (2 * Real.arctan R)) * (S.N Y : ℝ)) ^ 2 ≤ pairSum S Y t := by
  let a (j : S.index) : ℂ := (S.mult j : ℂ)
  have henergy := lorentz_pair_lower_bound (S.cut Y) S.gamma a (R := R) (Y := Y)
    (fun j hj => ⟨(S.gamma_pos j).le, mem_cut.mp hj⟩)
  have hnorm : (∑ j ∈ S.cut Y, ‖a j‖) = (S.N Y : ℝ) := by
    simp [a, Spectrum.N, Nat.cast_sum]
  have hsum : ‖∑ j ∈ S.cut Y, a j‖ = (S.N Y : ℝ) := by
    have hcast : (∑ j ∈ S.cut Y, a j) = (S.N Y : ℂ) := by
      simp only [a, Spectrum.N, Nat.cast_sum]
    rw [hcast]
    exact Complex.norm_natCast _
  rw [hnorm, hsum, show (S.N Y : ℝ) - (1 - Real.pi⁻¹ * (2 * Real.arctan R)) * (S.N Y : ℝ) =
    (Real.pi⁻¹ * (2 * Real.arctan R)) * (S.N Y : ℝ) by ring,
    max_eq_left (by positivity [Real.arctan_nonneg.mpr hR])] at henergy
  refine henergy.trans_eq ?_
  unfold pairSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hcos (k : S.index) (hk : k ∈ S.cut Y) : Real.cos (S.gamma k * t) = 0 := by
    have h := Real.sin_sq_add_cos_sq (S.gamma k * t)
    rw [halign k hk] at h
    nlinarith
  have hphase : Real.cos ((S.gamma i - S.gamma j) * t) = 1 := by
    rw [sub_mul, Real.cos_sub, hcos i hi, hcos j hj, halign i hi, halign j hj]
    norm_num
  simp [pairCos, hphase, a, Complex.mul_re]

private theorem eventually_lower_of_alignment (S : Spectrum) (hN : CountAsymptotic S)
    {κ : ℝ} (hκ : κ < threshold) :
    ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ, (∀ j ∈ S.cut Y, Real.sin (S.gamma j * t) = 1) →
      κ * (Y * Real.log Y ^ 2) < pairSum S Y t := by
  have hatan : Tendsto (fun Y : ℝ => Real.pi⁻¹ * (2 * Real.arctan (Real.sqrt Y)))
      atTop (𝓝 1) := by
    have h := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      Real.tendsto_sqrt_atTop
    have hlim : Real.pi⁻¹ * (2 * (Real.pi / 2)) = 1 := by
      field_simp [Real.pi_ne_zero]
    simpa only [Function.comp_apply, hlim] using (h.const_mul (2 : ℝ)).const_mul Real.pi⁻¹
  let L (Y : ℝ) := 2 * Real.pi / (1 + 2 / Real.sqrt Y) *
    ((Real.pi⁻¹ * (2 * Real.arctan (Real.sqrt Y))) * ((S.N Y : ℝ) / (Y * Real.log Y))) ^ 2
  have hwidth : Tendsto (fun Y : ℝ => 1 + 2 / Real.sqrt Y) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      (((tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul (2 : ℝ)).const_add 1)
  have hlim : Tendsto L atTop (𝓝 threshold) := by
    have hconst : Tendsto (fun _ : ℝ => 2 * Real.pi) atTop (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds
    have h := (hconst.div hwidth one_ne_zero).mul ((hatan.mul hN).pow 2)
    simpa [L, threshold, c, div_eq_mul_inv] using h
  filter_upwards [hlim.eventually (lt_mem_nhds hκ), eventually_gt_atTop (1 : ℝ)]
    with Y hLY hY
  intro t ht
  have hY0 : 0 < Y := by linarith
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY0
  have hb : 0 < 1 + 2 / Real.sqrt Y := by positivity
  have heq : Y * (1 + 2 / Real.sqrt Y) = Y + 2 * Real.sqrt Y := by
    field_simp
    nlinarith [Real.sq_sqrt hY0.le]
  have hL : L Y * (Y * Real.log Y ^ 2) =
      (2 * Real.pi) / (Y + 2 * Real.sqrt Y) *
        ((Real.pi⁻¹ * (2 * Real.arctan (Real.sqrt Y))) * (S.N Y : ℝ)) ^ 2 := by
    rw [← heq]
    dsimp only [L]
    field_simp [hb.ne', hY0.ne', (Real.log_pos hY).ne']
  calc
    κ * (Y * Real.log Y ^ 2) < L Y * (Y * Real.log Y ^ 2) :=
      mul_lt_mul_of_pos_right hLY (mul_pos hY0 (pow_pos (Real.log_pos hY) _))
    _ ≤ pairSum S Y t := by rw [hL]; exact lower_of_alignment S hs.le ht

/-- A single bounded-discrepancy spectrum attains the upper coefficient in a fixed band. -/
theorem exists_sharp_count_discrepancy :
    ∃ (S : Spectrum) (D A : ℝ), 1 < A ∧
      (∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) - countMain (2 * Real.pi) Y| ≤ D) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ Y : ℝ in atTop,
        (∀ t : ℝ, pairSum S Y t ≤ (threshold + ε) * (Y * Real.log Y ^ 2)) ∧
        ∃ t ∈ Ioo (Real.log Y) (A * Real.log Y),
          (threshold - ε) * (Y * Real.log Y ^ 2) < pairSum S Y t := by
  obtain ⟨S, w, _, hw, ⟨D, _, hD⟩, _, _, hvisit⟩ :=
    SpectrumTwoTermCountAlignment.exists_two_term_count_alignment
  have hcount : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) - countMain (2 * Real.pi) Y| ≤ D := by
    filter_upwards [hD] with Y hY
    rwa [countMain, ← div_mul_eq_mul_div]
  let K : ℝ := 42 * Real.pi / Real.log 2
  have hK : 0 < K := div_pos (by positivity) (Real.log_pos (by norm_num))
  let A : ℝ := 1 + 2 * K
  refine ⟨S, D, A, by dsimp [A]; linarith, hcount, fun ε hε => ?_⟩
  have hlower := eventually_lower_of_alignment S (count_asymptotic_of_bounded_discrepancy S hcount)
    (sub_lt_self threshold hε)
  filter_upwards [pairSum_le_of_bounded_discrepancy S hcount hε, hlower, hvisit,
    eventually_ge_atTop (21 : ℝ)] with Y hupper hlow hY hY21
  refine ⟨hupper, ?_⟩
  obtain ⟨_, q, _, _, hphase, hwide⟩ := hY
  obtain ⟨m, hm⟩ := hwide (Real.log Y)
  let t := Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ))
  have hlog : Real.log (21 * Y) ≤ 2 * Real.log Y := by
    rw [Real.log_mul (by norm_num) (by linarith : Y ≠ 0)]
    linarith [Real.log_le_log (by norm_num : 0 < (21 : ℝ)) hY21]
  refine ⟨t, ⟨hm.1, hm.2.trans_le ?_⟩, hlow t ?_⟩
  · dsimp [A]
    linarith [mul_le_mul_of_nonneg_left hlog hK.le]
  have halign := hphase m Y le_rfl
  unfold sine mass at halign
  have hwpos (j : S.index) : 0 < w j := by rw [(hw j).2]; positivity [S.gamma_pos j]
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun j _ => mul_le_of_le_one_right (hwpos j).le (Real.sin_le_one (S.gamma j * t)))).mp halign
  intro j hj
  exact (mul_right_inj' (hwpos j).ne').mp (by simpa only [mul_one] using h j hj)

#print axioms exists_sharp_count_discrepancy

end D5.S3.Analytic.Oscillation.MontgomeryCountSharpness
