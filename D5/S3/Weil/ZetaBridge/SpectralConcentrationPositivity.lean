/- GID: D5/S3/Weil/ZetaBridge/SpectralConcentrationPositivity
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/SpectralConcentrationPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A spectral concentration threshold gives an explicit positive multiplier gap. -/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Spectral concentration positivity

The concentration is constructed as the supremum of normalized band energies
over the supported nonzero tests.  Splitting the weighted spectral integral
over the band and its complement gives the explicit lower bound and its strict
positivity consequence.

Library-search audit trail (2026-08-30):

* Exact-name and body-shape searches for spectral concentration suprema,
  normalized band-energy ratios, weighted multiplier lower bounds, and the
  coefficient `a - (a + b) * concentration` found no existing D5 owner.
* `D5.S3.Weil.ZetaBridge.SafeComplementFiniteIndex.safe_complement_gap` has the
  same integral-splitting pattern for a specialized completed-zeta multiplier,
  but does not state the general multiplier and concentration theorem.
* Pinned Mathlib supplies `setIntegral_le_integral`, `integral_add_compl`,
  `le_csSup`, and the ordered-field quotient lemmas used below; no theorem
  combines them into this certificate.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set

namespace D5.S3.Weil.ZetaBridge.SpectralConcentrationPositivity

/-- For an `L2`-style test carrier with a Plancherel-normalized nonnegative
spectral density, the supremal energy concentration in `B` controls every
real multiplier bounded below by `a` off `B` and by `-b` on `B`.  The public
statement constructs both the concentration and the weighted quadratic form. -/
theorem spectral_concentration_positivity_certificate
    {Test : Type*} [Zero Test]
    (supportedIn : Real -> Test -> Prop)
    (spatialMass : Test -> Real)
    (spectralDensity : Test -> Real -> Real)
    (M : Real -> Real) (B : Set Real) (L a b : Real)
    (hB : MeasurableSet B)
    (ha : 0 < a) (hb : 0 <= b)
    (hOutside : forall xi, xi ∉ B -> a <= M xi)
    (hInside : forall xi, xi ∈ B -> -b <= M xi)
    (hDensityIntegrable : forall f, Integrable (spectralDensity f))
    (hWeightedIntegrable : forall f,
      Integrable (fun xi => M xi * spectralDensity f xi))
    (hDensityNonnegative : forall f xi, 0 <= spectralDensity f xi)
    (hPlancherel : forall f,
      (1 / (2 * Real.pi)) *
        (∫ xi : Real, spectralDensity f xi) = spatialMass f)
    (hZeroDensity : forall xi, spectralDensity 0 xi = 0)
    (hMassPositive : forall f, f ≠ 0 -> 0 < spatialMass f) :
    let concentrationRatios := {ratio : Real | exists f : Test,
      f ≠ 0 /\ supportedIn L f /\
        ratio = ((1 / (2 * Real.pi)) *
          ∫ xi : Real in B, spectralDensity f xi) / spatialMass f}
    let concentration := sSup concentrationRatios
    let quadraticForm := fun f : Test =>
      (1 / (2 * Real.pi)) *
        ∫ xi : Real, M xi * spectralDensity f xi
    (forall f, supportedIn L f ->
      (a - (a + b) * concentration) * spatialMass f <= quadraticForm f) /\
    (concentration < a / (a + b) ->
      forall f, f ≠ 0 -> supportedIn L f -> 0 < quadraticForm f) := by
  dsimp only
  let factor : Real := 1 / (2 * Real.pi)
  let concentrationRatios : Set Real := {ratio | exists f : Test,
    f ≠ 0 /\ supportedIn L f /\
      ratio = (factor * ∫ xi : Real in B, spectralDensity f xi) / spatialMass f}
  let concentration := sSup concentrationRatios
  let quadraticForm := fun f : Test =>
    factor * ∫ xi : Real, M xi * spectralDensity f xi
  have hFactorPositive : 0 < factor := by
    dsimp only [factor]
    positivity
  have hRatiosBounded : BddAbove concentrationRatios := by
    refine ⟨1, ?_⟩
    rintro ratio ⟨f, hf, _hSupport, hRatio⟩
    rw [hRatio]
    have hMass : 0 < spatialMass f := hMassPositive f hf
    apply (div_le_iff₀ hMass).2
    have hRestricted :
        (∫ xi : Real in B, spectralDensity f xi) <=
          ∫ xi : Real, spectralDensity f xi :=
      setIntegral_le_integral (hDensityIntegrable f)
        (Filter.Eventually.of_forall (hDensityNonnegative f))
    have hScaled := mul_le_mul_of_nonneg_left hRestricted hFactorPositive.le
    rw [hPlancherel f] at hScaled
    simpa only [one_mul] using hScaled
  have hConcentration (f : Test) (hSupport : supportedIn L f) :
      factor * (∫ xi : Real in B, spectralDensity f xi) <=
        concentration * spatialMass f := by
    by_cases hf : f = 0
    · subst f
      have hMassZero : spatialMass (0 : Test) = 0 := by
        symm
        simpa only [hZeroDensity, integral_zero, mul_zero] using hPlancherel (0 : Test)
      simp only [hZeroDensity, integral_zero, mul_zero, hMassZero, le_refl]
    · have hMass : 0 < spatialMass f := hMassPositive f hf
      have hRatioMem :
          (factor * (∫ xi : Real in B, spectralDensity f xi)) / spatialMass f ∈
            concentrationRatios :=
        ⟨f, hf, hSupport, rfl⟩
      have hRatioLe :
          (factor * (∫ xi : Real in B, spectralDensity f xi)) / spatialMass f <=
            concentration :=
        le_csSup hRatiosBounded hRatioMem
      exact (div_le_iff₀ hMass).mp hRatioLe
  have hLower (f : Test) (hSupport : supportedIn L f) :
      (a - (a + b) * concentration) * spatialMass f <= quadraticForm f := by
    let energy : Real -> Real := spectralDensity f
    have hEnergyIntegrable : Integrable energy := hDensityIntegrable f
    have hWeighted : Integrable (fun xi => M xi * energy xi) :=
      hWeightedIntegrable f
    have hEnergyNonnegative (xi : Real) : 0 <= energy xi :=
      hDensityNonnegative f xi
    have hInsideIntegral :
        (-b) * (∫ xi : Real in B, energy xi) <=
          ∫ xi : Real in B, M xi * energy xi := by
      rw [← integral_const_mul]
      apply integral_mono_ae
      · exact (hEnergyIntegrable.const_mul (-b)).integrableOn
      · exact hWeighted.integrableOn
      · filter_upwards [self_mem_ae_restrict hB] with xi hxi
        exact mul_le_mul_of_nonneg_right (hInside xi hxi) (hEnergyNonnegative xi)
    have hOutsideIntegral :
        a * (∫ xi : Real in Bᶜ, energy xi) <=
          ∫ xi : Real in Bᶜ, M xi * energy xi := by
      rw [← integral_const_mul]
      apply integral_mono_ae
      · exact (hEnergyIntegrable.const_mul a).integrableOn
      · exact hWeighted.integrableOn
      · filter_upwards [self_mem_ae_restrict hB.compl] with xi hxi
        exact mul_le_mul_of_nonneg_right (hOutside xi hxi) (hEnergyNonnegative xi)
    have hInsideScaled :
        -b * (factor * ∫ xi : Real in B, energy xi) <=
          factor * ∫ xi : Real in B, M xi * energy xi := by
      nlinarith [mul_le_mul_of_nonneg_left hInsideIntegral hFactorPositive.le]
    have hOutsideScaled :
        a * (factor * ∫ xi : Real in Bᶜ, energy xi) <=
          factor * ∫ xi : Real in Bᶜ, M xi * energy xi := by
      nlinarith [mul_le_mul_of_nonneg_left hOutsideIntegral hFactorPositive.le]
    have hEnergySplit :
        factor * (∫ xi : Real in B, energy xi) +
          factor * (∫ xi : Real in Bᶜ, energy xi) = spatialMass f := by
      rw [← mul_add, integral_add_compl hB hEnergyIntegrable]
      exact hPlancherel f
    have hWeightedSplit :
        factor * (∫ xi : Real in B, M xi * energy xi) +
          factor * (∫ xi : Real in Bᶜ, M xi * energy xi) = quadraticForm f := by
      rw [← mul_add, integral_add_compl hB hWeighted]
    have hBand : factor * (∫ xi : Real in B, energy xi) <=
        concentration * spatialMass f := by
      simpa only [energy] using hConcentration f hSupport
    have hBandScaled :
        (a + b) * (factor * ∫ xi : Real in B, energy xi) <=
          (a + b) * (concentration * spatialMass f) :=
      mul_le_mul_of_nonneg_left hBand (add_nonneg ha.le hb)
    nlinarith
  refine ⟨hLower, ?_⟩
  intro hThreshold f hf hSupport
  have hDenominator : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
  have hGap : 0 < a - (a + b) * concentration := by
    have hScaled := (lt_div_iff₀ hDenominator).mp hThreshold
    nlinarith
  exact (mul_pos hGap (hMassPositive f hf)).trans_le (hLower f hSupport)

#print axioms spectral_concentration_positivity_certificate

end D5.S3.Weil.ZetaBridge.SpectralConcentrationPositivity
