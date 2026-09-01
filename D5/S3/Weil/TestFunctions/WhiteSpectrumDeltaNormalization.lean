/- GID: D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized angular white spectrum has inverse Fourier transform equal to Dirac mass. -/

import D5.S3.Weil.TestFunctions.WhiteToHaarIdentity
import Mathlib.Analysis.Distribution.TemperedDistribution

/- Library-search audit trail (2026-09-01):
   * D5 searches for white spectrum, budget frontiers, spectral measures, and
     normalized Lebesgue Fourier identities found `WhiteToHaarIdentity`, whose
     `normalizedLebesgueSpectrum` is reused below, but no inverse-Fourier-to-Dirac theorem.
   * The neighboring `ResolventFrontierGeometry` parameterizes its white-floor
     budget estimate, while atom 43fbb5... separately owns the exact resolvent
     cost. Neither supplies the distributional identity proved here.
   * Pinned Mathlib supplies `Real.smul_map_volume_mul_left`,
     `TemperedDistribution.fourier_delta_zero`, and the Fourier-pair inverse law.
     These are applied directly instead of reproving measure scaling or Fourier inversion.
   * Searches across the pinned third-party dependency closure found no theorem
     combining the repository's angular-frequency convention with this normalized measure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace D5.S3.Weil.TestFunctions.WhiteSpectrumDeltaNormalization

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions.WhiteToHaarIdentity

/-- Push an angular-frequency measure through `xi |-> xi / (2 * pi)`, the coordinate used by
Mathlib's `2 * pi` Fourier kernel. -/
noncomputable def angularFrequencyPushforward (nu : Measure Real) : Measure Real :=
  Measure.map mathlibFrequency nu

/-- The source white spectrum `d xi / (2 * pi)` becomes ordinary Lebesgue measure after the
angular-to-Mathlib frequency change. -/
theorem normalized_white_frequency_pushforward :
    angularFrequencyPushforward normalizedLebesgueSpectrum = volume := by
  have scalePositive : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have scaleNonzero : (2 * Real.pi)⁻¹ ≠ 0 := scalePositive.ne'
  have frequencyFormula : mathlibFrequency = fun xi : Real => (2 * Real.pi)⁻¹ * xi := by
    funext xi
    rw [mathlibFrequency]
    ring
  rw [angularFrequencyPushforward, normalizedLebesgueSpectrum, Measure.map_smul,
    frequencyFormula]
  simpa only [one_div, abs_of_pos scalePositive] using
    (Real.smul_map_volume_mul_left scaleNonzero)

private noncomputable instance normalizedWhitePushforwardHasTemperateGrowth :
    (angularFrequencyPushforward normalizedLebesgueSpectrum).HasTemperateGrowth := by
  rw [normalized_white_frequency_pushforward]
  infer_instance

/-- The inverse angular Fourier transform of a measure is Mathlib's inverse Fourier transform
after changing from angular frequency to its `2 * pi` frequency coordinate. -/
noncomputable def inverseAngularFourier
    (nu : Measure Real) [(angularFrequencyPushforward nu).HasTemperateGrowth] :
    𝓢'(Real, Complex) :=
  𝓕⁻ (angularFrequencyPushforward nu).toTemperedDistribution

/-- The normalized angular white spectrum `d xi / (2 * pi)` has inverse Fourier transform equal
to the Dirac distribution at zero. -/
theorem normalized_white_spectrum_inverse_fourier :
    inverseAngularFourier normalizedLebesgueSpectrum =
      TemperedDistribution.delta (0 : Real) := by
  have pushforwardDistribution :
      (angularFrequencyPushforward normalizedLebesgueSpectrum).toTemperedDistribution =
        (volume : Measure Real).toTemperedDistribution := by
    ext test
    simp only [Measure.toTemperedDistribution_apply]
    rw [normalized_white_frequency_pushforward]
  rw [inverseAngularFourier, pushforwardDistribution]
  have transformed := congrArg (fun distribution : 𝓢'(Real, Complex) => 𝓕⁻ distribution)
    (TemperedDistribution.fourier_delta_zero (E := Real))
  simpa using transformed.symm

/-- Concrete positive probe: the repository's normalized white spectrum realizes the identity. -/
example :
    inverseAngularFourier normalizedLebesgueSpectrum =
      TemperedDistribution.delta (0 : Real) :=
  normalized_white_spectrum_inverse_fourier

/-- Concrete negative probe: the zero measure does not satisfy the required white normalization. -/
example : angularFrequencyPushforward (0 : Measure Real) ≠ volume := by
  rw [angularFrequencyPushforward, Measure.map_zero]
  intro equality
  have intervalEquality := congrArg (fun mu : Measure Real => mu (Set.Ioc 0 1)) equality
  norm_num at intervalEquality

#print axioms angularFrequencyPushforward
#print axioms normalized_white_frequency_pushforward
#print axioms inverseAngularFourier
#print axioms normalized_white_spectrum_inverse_fourier

end D5.S3.Weil.TestFunctions.WhiteSpectrumDeltaNormalization
