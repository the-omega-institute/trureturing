/- GID: D5/S3/Weil/PrimeAddress/PrimePowerDiffractionAtom
   generality: I
   mirror-B: D5/B/S3/Weil/PrimeAddress/PrimePowerDiffractionAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalize the explicit-formula summand at every positive prime-power address. -/

import D5.S3.Weil.PrimePoleTerms

/- Library-search audit trail (2026-09-04):
   * Repository searches for prime-power diffraction, logarithmic addresses, von Mangoldt
     weights, and generalized explicit-formula summand normalizations found the adjacent
     definition `PrimePoleTerms.primeSummand`, but no theorem normalizing all its factors.
   * Exact pinned-Mathlib hits `ArithmeticFunction.vonMangoldt_apply_pow` and
     `ArithmeticFunction.vonMangoldt_apply_prime` normalize the arithmetic coefficient.
   * Exact pinned-Mathlib hits `Real.log_pow`, `Real.rpow_mul`, and `Real.rpow_natCast`
     normalize the logarithmic location and real-power weight and are reused below.
   * The exponent is positive as a natural number and the base is prime, so no totalized
     logarithm or zero-base real-power branch is used.
-/

namespace D5.S3.Weil.PrimeAddress.PrimePowerDiffractionAtom

open D5.S3.Weil.PrimePoleTerms D5.S3.Weil.TestFunctions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- At a positive prime-power address, the explicit-formula summand is located at
`m * log p` and has arithmetic weight `log p * p ^ (-m / 2)`. This is the precise
prime-power atom supplied by the explicit formula; it makes no assertion that a zero
set is a quasicrystal or that such a characterization is equivalent to RH. -/
theorem prime_power_diffraction_atom
    (g : WeilTestFunction) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    Real.log (((p ^ m : ℕ) : ℝ)) = (m : ℝ) * Real.log p ∧
      (ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) *
          (((p ^ m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        Real.log p * (p : ℝ) ^ (-((m : ℝ) / 2)) ∧
      primeSummand g (p ^ m) =
        ((Real.log p : ℝ) : ℂ) * (((p : ℝ) ^ (-((m : ℝ) / 2)) : ℝ) : ℂ) *
          (g ((m : ℝ) * Real.log p) + g (-((m : ℝ) * Real.log p))) := by
  have hlocation : Real.log (((p ^ m : ℕ) : ℝ)) = (m : ℝ) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hLambda : ArithmeticFunction.vonMangoldt (p ^ m) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hm,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpNonneg : 0 ≤ (p : ℝ) := by positivity
  have hpower :
      (((p ^ m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        (p : ℝ) ^ (-((m : ℝ) / 2)) := by
    calc
      (((p ^ m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
          (((p : ℝ) ^ (m : ℕ)) ^ (-(1 / 2 : ℝ))) := by rw [Nat.cast_pow]
      _ = (((p : ℝ) ^ (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
        rw [Real.rpow_natCast]
      _ = (p : ℝ) ^ ((m : ℝ) * (-(1 / 2 : ℝ))) := by
        rw [Real.rpow_mul hpNonneg]
      _ = (p : ℝ) ^ (-((m : ℝ) / 2)) := by
        congr 1
        ring
  refine ⟨hlocation, ?_, ?_⟩
  · rw [hLambda, hpower]
  · rw [primeSummand, hLambda, hpower, hlocation]

#print axioms prime_power_diffraction_atom

end

end D5.S3.Weil.PrimeAddress.PrimePowerDiffractionAtom
