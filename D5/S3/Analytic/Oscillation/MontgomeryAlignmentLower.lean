/- GID: D5/S3/Analytic/Oscillation/MontgomeryAlignmentLower
   generality: I
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryAlignmentLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact alignment and the leading count give the sharp Cauchy lower coefficient. -/

import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
import D5.S3.Fourier.Concentration.CauchyPairEnergy

/-! Aligned spectra attain the Cauchy lower coefficient from the counting asymptotic. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomeryAlignmentLower

open OrdinateCounting (Spectrum CountAsymptotic)
open SpectrumPhaseCutoff (mem_cut)
open MontgomeryWindow (montgomery pairCos montgomery_normalization)
open D5.S3.Fourier.Concentration.CauchyPairEnergy (lorentz_pair_lower_bound)

private abbrev c : ℝ := 1 / (2 * Real.pi)
private abbrev threshold : ℝ := 2 * Real.pi * c ^ 2

private theorem lower_of_alignment (S : Spectrum) {Y R t : ℝ} (hY : 1 < Y)
    (hR : 0 ≤ R)
    (halign : ∀ i ∈ S.cut Y, ∀ j ∈ S.cut Y, Real.cos ((S.gamma i - S.gamma j) * t) = 1) :
    (2 * Real.pi) / (Y + 2 * R) *
      ((Real.pi⁻¹ * (2 * Real.arctan R)) * (S.N Y : ℝ)) ^ 2 ≤
        Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y := by
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
  rw [← montgomery_normalization S hY t]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [pairCos, halign i hi j hj, a, Complex.mul_re]

/-- Under the counting asymptotic, exact phase alignment forces the ordered Lorentz pair sum above
any coefficient strictly below the Cauchy threshold at every sufficiently large cutoff. -/
theorem eventually_montgomery_gt_of_phase_alignment (S : Spectrum) (hN : CountAsymptotic S)
    {κ : ℝ} (hκ : κ < threshold) :
    ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
      (∀ i ∈ S.cut Y, ∀ j ∈ S.cut Y, Real.cos ((S.gamma i - S.gamma j) * t) = 1) →
      κ * (Y * Real.log Y ^ 2) <
        Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y := by
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
    _ ≤ Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y := by
      rw [hL]
      exact lower_of_alignment S hY hs.le ht

#print axioms eventually_montgomery_gt_of_phase_alignment

end D5.S3.Analytic.Oscillation.MontgomeryAlignmentLower
