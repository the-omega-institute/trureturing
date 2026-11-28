import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Integral.Layercake
import OmegaBuild.Commands

/-!
Omega original.

Centered interval mass bounds for the scale-two Lorentz kernel.
-/

compile_only_with_mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section

namespace Omega.MeasureTheory.LorentzIntervalMass

/-- The Lorentz kernel of scale two, normalized to equal one at the origin. -/
def kernel (x : ℝ) : ℝ := 4 / (4 + x ^ 2)

private theorem kernel_eq_two_cauchy (x : ℝ) :
    kernel x = (2 * Real.pi) * cauchyPDFReal 0 2 x := by
  rw [kernel, cauchyPDFReal_def]
  simp only [sub_zero, NNReal.coe_ofNat]
  have h : (4 : ℝ) + x ^ 2 ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, h]
  ring

private theorem kernel_integral :
    (∫ x : ℝ, kernel x) = 2 * Real.pi := by
  simp_rw [kernel_eq_two_cauchy]
  rw [integral_const_mul, integral_cauchyPDFReal_eq_one 0 (by norm_num : (2 : ℝ≥0) ≠ 0), mul_one]

theorem kernel_level {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    {x : ℝ | t ≤ kernel x} = Icc (-(2 * Real.sqrt (1 / t - 1))) (2 * Real.sqrt (1 / t - 1)) := by
  have hs : 0 ≤ 1 / t - 1 := sub_nonneg.mpr ((le_div_iff₀ h0).mpr (by simpa using h1))
  ext x
  have hd : 0 < 4 + x ^ 2 := by positivity
  have hrad : 0 ≤ 2 * Real.sqrt (1 / t - 1) := by positivity
  rw [mem_ofPred_eq, kernel, le_div_iff₀ hd, mem_Icc]
  constructor
  · intro h
    have hx : x ^ 2 ≤ (2 * Real.sqrt (1 / t - 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hs]
      apply (mul_le_mul_iff_right₀ h0).mp
      have he : t * (2 ^ 2 * (1 / t - 1)) = 4 - 4 * t := by field_simp; ring
      rw [he]
      nlinarith only [h]
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨hl, hr⟩
    have hx : x ^ 2 ≤ (2 * Real.sqrt (1 / t - 1)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ 2 * Real.sqrt (1 / t - 1) + x)]
    rw [mul_pow, Real.sq_sqrt hs] at hx
    have h := mul_le_mul_of_nonneg_left hx h0.le
    have he : t * (2 ^ 2 * (1 / t - 1)) = 4 - 4 * t := by field_simp; ring
    rw [he] at h
    nlinarith only [h]

open scoped ENNReal

theorem kernel_nonneg (x : ℝ) : 0 ≤ kernel x := by
  unfold kernel
  positivity

private theorem kernel_le_one (x : ℝ) : kernel x ≤ 1 := by
  rw [kernel, div_le_one (by positivity)]
  linarith [sq_nonneg x]

private def levelMass (μ : Measure ℝ) (t : ℝ) : ℝ :=
  μ.real {x : ℝ | t ≤ kernel x}

private theorem levelMass_integrableOn (μ : Measure ℝ) (hint : Integrable kernel μ) :
    IntegrableOn (levelMass μ) (Ioc 0 1) := by
  have hn : 0 ≤ᵐ[μ] kernel := Filter.Eventually.of_forall kernel_nonneg
  have he := lintegral_eq_lintegral_meas_le μ hn hint.aemeasurable
  have hfin : (∫⁻ t in Ioi (0 : ℝ), μ {x : ℝ | t ≤ kernel x}) < ∞ := by
    rw [← he]
    exact hint.lintegral_lt_top
  have h_anti : Antitone (fun t : ℝ => μ {x : ℝ | t ≤ kernel x}) :=
    fun _ _ h => measure_mono (fun _ hx => h.trans hx)
  have hi : IntegrableOn (levelMass μ) (Ioi 0) := by
    refine ⟨h_anti.measurable.ennreal_toReal.aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono
    intro t
    simpa only [levelMass, measureReal_def, Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
      (ENNReal.ofReal_toReal_le : ENNReal.ofReal (μ {x : ℝ | t ≤ kernel x}).toReal ≤ _)
  exact hi.mono_set Ioc_subset_Ioi_self

/-- A uniform centered interval mass bound controls the Lorentz integral. -/
theorem lorentz_mass_upper (μ : Measure ℝ) (hint : Integrable kernel μ)
    {ρ B : ℝ} (hloc : ∀ r ≥ 0, μ.real (Icc (-r) r) ≤ 2 * ρ * r + B) :
    (∫ x, kernel x ∂μ) ≤ 2 * Real.pi * ρ + B := by
  have hvol : Integrable kernel := by
    rw [show kernel = (fun x => (2 * Real.pi) * cauchyPDFReal 0 2 x) from
      funext kernel_eq_two_cauchy]
    exact (integrable_cauchyPDFReal 0).const_mul _
  have hμeq := hint.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall kernel_nonneg) (Filter.Eventually.of_forall kernel_le_one)
  have hveq := hvol.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall kernel_nonneg) (Filter.Eventually.of_forall kernel_le_one)
  change (∫ x, kernel x ∂μ) = ∫ t in Ioc 0 1, levelMass μ t at hμeq
  change (∫ x, kernel x) = ∫ t in Ioc 0 1, levelMass volume t at hveq
  have hb : IntegrableOn (fun _ : ℝ => B) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  rw [hμeq]
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, ρ * levelMass volume t + B := by
      apply setIntegral_mono_on (levelMass_integrableOn μ hint)
        (((levelMass_integrableOn volume hvol).const_mul ρ).add hb) measurableSet_Ioc
      intro t ht
      change μ.real {x : ℝ | t ≤ kernel x} ≤ ρ * volume.real {x : ℝ | t ≤ kernel x} + B
      rw [kernel_level ht.1 ht.2, Real.volume_real_Icc]
      have hr : 0 ≤ 2 * Real.sqrt (1 / t - 1) := by positivity
      rw [max_eq_left (show 0 ≤ 2 * Real.sqrt (1 / t - 1) -
        -(2 * Real.sqrt (1 / t - 1)) by linarith)]
      convert hloc (2 * Real.sqrt (1 / t - 1)) hr using 1
      ring
    _ = _ := by
      rw [integral_add ((levelMass_integrableOn volume hvol).const_mul ρ)
        hb, integral_const_mul, ← hveq,
        kernel_integral, setIntegral_const, Real.volume_real_Ioc]
      norm_num [smul_eq_mul]
      ring


/-- The weighted mass in centered intervals bounds each finite Lorentz sum. -/
theorem lorentz_sum_upper {J : Type*} (s : Finset J) (x w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) {ρ B : ℝ}
    (hloc : ∀ r ≥ 0, (∑ j ∈ s, if x j ∈ Icc (-r) r then w j else 0) ≤
      2 * ρ * r + B) :
    (∑ j ∈ s, w j * kernel (x j)) ≤ 2 * Real.pi * ρ + B := by
  classical
  let ν (j : J) : Measure ℝ := ENNReal.ofReal (w j) • Measure.dirac (x j)
  let μ : Measure ℝ := ∑ j ∈ s, ν j
  have hint (j : J) : Integrable kernel (ν j) :=
    (integrable_dirac (by finiteness : ‖kernel (x j)‖ₑ < ∞)).smul_measure
      ENNReal.ofReal_ne_top
  have hμ : Integrable kernel μ := integrable_finsetSum_measure.2 fun j _ => hint j
  have hmeasure (r : ℝ) : μ.real (Icc (-r) r) =
      ∑ j ∈ s, if x j ∈ Icc (-r) r then w j else 0 := by
    dsimp only [μ]
    rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hx : x j ∈ Icc (-r) r
      · simp [ν, Measure.smul_apply, Measure.dirac_apply_of_mem hx, hx, hw j hj]
      · simp [ν, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc, hx]
    · intro j hj
      by_cases hx : x j ∈ Icc (-r) r <;>
        simp [ν, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc, hx]
  have hsum : (∫ t, kernel t ∂μ) = ∑ j ∈ s, w j * kernel (x j) := by
    dsimp only [μ]
    rw [integral_finsetSum_measure fun j _ => hint j]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ν, integral_smul_measure, integral_dirac, hw j hj]
  rw [← hsum]
  exact lorentz_mass_upper μ hμ fun r hr => (hmeasure r).trans_le (hloc r hr)

end Omega.MeasureTheory.LorentzIntervalMass
