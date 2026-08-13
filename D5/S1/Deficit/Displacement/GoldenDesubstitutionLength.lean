/- GID: D5/S1/Deficit/Displacement/GoldenDesubstitutionLength
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenDesubstitutionLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Defines the hidden product nS by applying the golden substitution start to every prime exponent, proves its factorization is the pointwise substituted factorization, and lifts that fact to the expansion-face length: lambdaPlus (nS n) is the prime-log sum of betaReal at the displacement decodes of the exponents. Consequently, for n nonzero, lambdaPlus (nS n) minus lambdaPlus n is the corresponding sum of exponentwise displacement increments. -/

import D5.S1.Deficit.DoubleFaceLength
import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf

open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf

namespace GoldenDesubstitutionLength

private theorem betaReal_zero : betaReal 0 = 0 := by
  simp [betaReal, betaGolden, betaDigits,
    D5.S1.Digit.Z, D5.S1.Digit.toRaw,
    D5.S0.Conventions.wEncoding, Nat.zeckendorfEquiv,
    D5.S1.Digit.rawOfZeckendorf]

/-- The hidden product obtained by applying the golden substitution start to every prime
exponent. -/
def nS (n : ℕ) : ℕ :=
  n.factorization.prod fun p exponent ↦ p ^ goldenSubstStart exponent

/-- The prime factorization of `nS n` is the pointwise golden substitution of the factorization
of `n`. -/
theorem nS_factorization (n : ℕ) :
    (nS n).factorization =
      Finsupp.mapRange goldenSubstStart goldenSubstStart_zero n.factorization := by
  rw [nS, ← Finsupp.prod_mapRange_index
    (f := goldenSubstStart) (hf := goldenSubstStart_zero) (fun p ↦ pow_zero p)]
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using Finsupp.support_mapRange hp)

/-- The expansion-face length of the substituted product expands by applying
`goldenSubstStart` to every original prime exponent. -/
theorem lambdaPlus_nS_expansion (n : ℕ) :
    lambdaPlus (nS n) =
      n.factorization.sum fun p exponent ↦
        betaReal (goldenSubstStart exponent) * Real.log p := by
  rw [lambdaPlus, nS_factorization]
  rw [Finsupp.sum_mapRange_index (f := goldenSubstStart) (hf := goldenSubstStart_zero)]
  intro p
  rw [betaReal_zero, zero_mul]

/-- Golden desubstitution reads the substituted exponents as Zeckendorf displacements in the
expansion-face length. -/
theorem lambdaPlus_nS_eq_displacement_sum (n : ℕ) :
    lambdaPlus (nS n) =
      n.factorization.sum fun p exponent ↦
        betaReal (displacementDecode exponent) * Real.log p := by
  rw [lambdaPlus_nS_expansion]
  exact Finsupp.sum_congr fun _ _ ↦ by
    rw [golden_subst_start_eq_displacement_decode]

/-- For nonzero `n`, substitution changes the expansion-face length by the prime-log sum of the
Zeckendorf displacement increments of its exponents. -/
theorem lambdaPlus_nS_sub_lambdaPlus (n : ℕ) (_hn : n ≠ 0) :
    lambdaPlus (nS n) - lambdaPlus n =
      n.factorization.sum fun p exponent ↦
        (betaReal (displacementDecode exponent) - betaReal exponent) * Real.log p := by
  rw [lambdaPlus_nS_eq_displacement_sum, lambdaPlus, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun _ _ ↦ by ring

example : lambdaPlus (nS 1) - lambdaPlus 1 = 0 := by
  rw [lambdaPlus_nS_sub_lambdaPlus 1 one_ne_zero]
  simp

end GoldenDesubstitutionLength
