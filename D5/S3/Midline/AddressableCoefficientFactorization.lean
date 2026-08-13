/- GID: D5/S3/Midline/AddressableCoefficientFactorization
   generality: I
   mirror-B: D5/B/S3/Midline/AddressableCoefficientFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Addressable zeta coefficients split into half-density, phase, and scaling factors. -/

import D5.S3.Weil.SpectralDynamics

namespace D5.S3.Midline.AddressableCoefficientFactorization

open D5.S1.Digit
open D5.S3.Weil.SpectralDynamics
open D5.S3.Weil.SpectralHilbert

/-- At every prime-axis address, the coefficient at `s = 1/2 + delta + i t`
splits into the critical half-density coefficient, the public vertical phase,
and the public horizontal scaling weight. This is only a pointwise coefficient
identity; it makes no assertion about a sum or its analytic continuation. -/
theorem addressable_coefficient_factorization (delta t : ℝ) (a : PrimeAxisTable) :
    labeledZetaCoefficient
        (((1 / 2 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)) a =
      labeledZetaCoefficient ((1 / 2 : ℝ) : ℂ) a *
        verticalPhase t a * horizontalWeight delta a := by
  have hn : ((((primeAxisEncoding a : ℕ+) : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (PNat.pos (primeAxisEncoding a)))
  rw [show (((1 / 2 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
      (((1 / 2 : ℝ) : ℂ) + (Complex.I * (t : ℂ) + (delta : ℂ))) by
    push_cast
    ring]
  simp only [labeledZetaCoefficient, verticalPhase, horizontalWeight]
  rw [Complex.cpow_add _ _ hn, Complex.cpow_add _ _ hn]
  simp only [one_div, mul_inv_rev]
  ring

example : PrimeAxisTable := ⟨0, by simp [CanonicalRaw]⟩

example :
    let a : PrimeAxisTable := ⟨0, by simp [CanonicalRaw]⟩
    labeledZetaCoefficient
        (((1 / 2 + (0 : ℝ) : ℝ) : ℂ) + Complex.I * (0 : ℂ)) a =
      labeledZetaCoefficient ((1 / 2 : ℝ) : ℂ) a *
        verticalPhase 0 a * horizontalWeight 0 a := by
  dsimp only
  exact addressable_coefficient_factorization 0 0 ⟨0, by simp [CanonicalRaw]⟩

end D5.S3.Midline.AddressableCoefficientFactorization
