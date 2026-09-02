/- GID: D5/S3/PrimeObserver/ThreeCompletionFinalProposition
   generality: I
   mirror-B: D5/B/S3/PrimeObserver/ThreeCompletionFinalProposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime exponents, realizability mass, and operator phase form three distinct completions. -/

import D5.S3.Analytic.PrimeProducts.GlobalPrimeExponentRealizability
import D5.S3.ConceptDynamics.ObservationOrder.TypedPrimeLanguageHierarchy
import D5.S3.Factorization.ExponentCoordinates.PrimeExponentBijection

/- Library-search audit trail (2026-09-02):
   * Exact D5 owners are `prime_exponent_language_bijection`,
     `global_prime_exponent_realizable_iff`, `relative_phase_density_witness`, and
     `prime_diagonal_strictly_coarser_than_operator`; they are applied directly.
   * Name, symbol-variant, theorem-body, digestion-receipt, digest, and in-flight-branch
     searches found no theorem packaging these three completion levels.
   * The probability clause keeps the exact `1 < s` threshold, and the deterministic
     clause stays on positive naturals so zero cannot collapse with one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.PrimeObserver.ThreeCompletionFinalProposition

open D5.S3.Analytic.PrimeProducts.GlobalPrimeExponentRealizability
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.ObservationOrder.TypedPrimeLanguageHierarchy
open D5.S3.Factorization.ExponentCoordinates.PrimeExponentBijection

/-- The zeta prime-observer model has three noninterchangeable completions. Positive
naturals are exactly reconstructed from their finitely supported prime exponents. The
independent geometric exponent law is globally realizable exactly above `s = 1`. Even
then, a concrete pair of qubit states has the same commuting prime-diagonal readout but
different operators, and the diagonal language is strictly coarser than the operator
language. -/
theorem prime_observer_three_completion_final_proposition (s : Real) :
    Function.Bijective primeExponentLanguageEquiv ∧
      ((∃ q : PMF Nat, RealizesPrimeExponentLaw s q) ↔ 1 < s) ∧
      (relativePhaseDensityWitness.1 ≠ relativePhaseDensityWitness.2 ∧
        qubitPrimeDiagonalLanguage relativePhaseDensityWitness.1 =
          qubitPrimeDiagonalLanguage relativePhaseDensityWitness.2 ∧
        qubitOperatorLanguage relativePhaseDensityWitness.1 ≠
          qubitOperatorLanguage relativePhaseDensityWitness.2) ∧
      (Refines qubitPrimeDiagonalLanguage qubitOperatorLanguage ∧
        ¬Refines qubitOperatorLanguage qubitPrimeDiagonalLanguage) := by
  exact ⟨prime_exponent_language_bijection,
    global_prime_exponent_realizable_iff s,
    relative_phase_density_witness,
    prime_diagonal_strictly_coarser_than_operator⟩

#print axioms prime_observer_three_completion_final_proposition

end D5.S3.PrimeObserver.ThreeCompletionFinalProposition
