/- GID: D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reuses the hidden product nS and its pointwise substituted prime factorization, then lifts golden desubstitution to the conjugate face: lambdaMinus (nS n) is the prime-log sum of betaContraction at the displacement decodes of the exponents. Subtracting lambdaMinus n gives the corresponding sum of exponentwise conjugate-face displacement increments. -/

import D5.S1.Deficit.Displacement.GoldenDesubstitutionLength

open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf
open GoldenDesubstitutionLength

namespace GoldenDesubstitutionConjugateLength

private theorem betaContraction_zero : betaContraction 0 = 0 := by
  simp [betaContraction, betaGolden, betaDigits,
    D5.S1.Digit.Z, D5.S1.Digit.toRaw,
    D5.S0.Conventions.wEncoding, Nat.zeckendorfEquiv,
    D5.S1.Digit.rawOfZeckendorf]

private theorem lambdaMinus_nS_expansion (n : ℕ) :
    lambdaMinus (nS n) =
      n.factorization.sum fun p exponent ↦
        betaContraction (goldenSubstStart exponent) * Real.log p := by
  rw [lambdaMinus, nS_factorization]
  rw [Finsupp.sum_mapRange_index (f := goldenSubstStart) (hf := goldenSubstStart_zero)]
  intro p
  rw [betaContraction_zero, zero_mul]

/-- Golden desubstitution reads the substituted exponents as Zeckendorf displacements in the
conjugate-face length. -/
theorem lambdaMinus_nS_eq_displacement_sum (n : ℕ) :
    lambdaMinus (nS n) =
      n.factorization.sum fun p exponent ↦
        betaContraction (displacementDecode exponent) * Real.log p := by
  rw [lambdaMinus_nS_expansion]
  exact Finsupp.sum_congr fun _ _ ↦ by
    rw [golden_subst_start_eq_displacement_decode]

/-- Substitution changes the conjugate-face length by the prime-log sum of the Zeckendorf
displacement increments of its exponents. -/
theorem lambdaMinus_nS_sub_lambdaMinus (n : ℕ) :
    lambdaMinus (nS n) - lambdaMinus n =
      n.factorization.sum fun p exponent ↦
        (betaContraction (displacementDecode exponent) - betaContraction exponent) *
          Real.log p := by
  rw [lambdaMinus_nS_eq_displacement_sum, lambdaMinus, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun _ _ ↦ by ring

example : lambdaMinus (nS 1) - lambdaMinus 1 = 0 := by
  rw [lambdaMinus_nS_sub_lambdaMinus]
  simp

end GoldenDesubstitutionConjugateLength
