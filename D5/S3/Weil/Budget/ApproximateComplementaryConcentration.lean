/- GID: D5/S3/Weil/Budget/ApproximateComplementaryConcentration
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/ApproximateComplementaryConcentration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Residual spectral mass above a Fourier threshold is controlled by the energy gap. -/

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Complex.Basic

/- Library-search audit trail (2026-08-29):
   * D5 searches for approximate complementary concentration, residual
     spectral mass, Fourier near-zero concentration, and Rayleigh gaps found
     no exact frozen owner.
   * Body-shape searches for a positive measure of
     `{xi | delta <= ‖fourier xi‖}` controlled by its squared-energy integral
     found no D5 declaration or canonical local definition to reuse.
   * Pinned Mathlib exact hit `MeasureTheory.meas_ge_le_lintegral_div`
     is the measure-theoretic Markov inequality used below. The elementary
     `pow_le_pow_left'` lemma embeds the source's Fourier-modulus threshold
     set into the squared threshold set used by Markov's inequality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.ApproximateComplementaryConcentration

open MeasureTheory Set
open scoped ENNReal NNReal

/-- If the residual spectral energy of a measurable Fourier transform is
`epsilon`, then the residual measure of the region where its modulus is at
least `delta` is at most `epsilon / delta^2`. -/
theorem approximate_complementary_concentration
    (residual : Measure Real) (fourier : Real -> Complex)
    (fourierAEMeasurable : AEMeasurable fourier residual)
    (epsilon : ENNReal) (delta : NNReal) (deltaPositive : 0 < delta)
    (residualEnergy :
      lintegral residual (fun xi => ‖fourier xi‖ₑ ^ (2 : Nat)) = epsilon) :
    residual {xi | (delta : ENNReal) <= ‖fourier xi‖ₑ} <=
      epsilon / (delta : ENNReal) ^ (2 : Nat) := by
  calc
    residual {xi | (delta : ENNReal) <= ‖fourier xi‖ₑ} <=
        residual {xi | (delta : ENNReal) ^ (2 : Nat) <=
          ‖fourier xi‖ₑ ^ (2 : Nat)} := by
      apply measure_mono
      intro xi threshold
      change (delta : ENNReal) <= ‖fourier xi‖ₑ at threshold
      change (delta : ENNReal) ^ (2 : Nat) <=
        ‖fourier xi‖ₑ ^ (2 : Nat)
      exact pow_le_pow_left' threshold (2 : Nat)
    _ <= lintegral residual
          (fun xi => ‖fourier xi‖ₑ ^ (2 : Nat)) /
        (delta : ENNReal) ^ (2 : Nat) :=
      meas_ge_le_lintegral_div
        (fourierAEMeasurable.enorm.pow_const (2 : Nat))
        (ENNReal.pow_ne_zero
          (ENNReal.coe_ne_zero.mpr (ne_of_gt deltaPositive)) (2 : Nat))
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    _ = epsilon / (delta : ENNReal) ^ (2 : Nat) := by rw [residualEnergy]

#print axioms approximate_complementary_concentration

end D5.S3.Weil.Budget.ApproximateComplementaryConcentration
