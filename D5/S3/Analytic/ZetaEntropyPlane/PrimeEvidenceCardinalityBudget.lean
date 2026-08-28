/- GID: D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal prime-set size allows unbounded gaps; constant and empty sums audit. -/
/- Library-search audit trail (2026-08-25):
   * Repository inspection read the signatures of all 14 existing modules whose path or
     filename contains `Budget`. None compares finite evidence sums at equal cardinality.
     `GreenClassBudgetGeometry` instead makes one measure cardinality-determined, while
     `MinimumCompleteSetCover.budgetCost` only names a generic finite cost sum.
   * FPOD 234.1, `PrimeDensityEvidenceOrthogonality`, compares infinite-support counting
     limits with summability. It has no finite-cardinality or finite-sum conclusion.
   * FPOD 235.2, `PrimeEvidenceSharpThreshold`, owns `primeEvidence`; it is imported here.
     `SmallPrimeChannelOptimality` bounds fixed-cardinality sums under strict antitonicity,
     but does not give an unbounded gap between equal-cardinality sums.
   * Pinned Mathlib provides `Nat.exists_infinite_primes`, `exists_nat_gt`,
     `Finset.sum_const`, and `Real.rpow_one`; these are reused below. -/

import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceCardinalityBudget

open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open scoped BigOperators

/-- The finite budget obtained by summing an evidence family over selected indices. -/
def finiteEvidenceBudget {Index : Type*} (evidence : Index -> Real)
    (indices : Finset Index) : Real :=
  ∑ index ∈ indices, evidence index

/-- An empty selection has zero budget for every evidence family. -/
theorem finite_evidence_budget_empty {Index : Type*} (evidence : Index -> Real) :
    finiteEvidenceBudget evidence ∅ = 0 := by
  simp [finiteEvidenceBudget]
#print axioms finite_evidence_budget_empty

/-- Every selection on the empty index type is empty and hence has zero budget. -/
theorem empty_index_budget_zero (evidence : Empty -> Real) (indices : Finset Empty) :
    finiteEvidenceBudget evidence indices = 0 := by
  have indices_empty : indices = ∅ := by
    ext index
    exact index.elim
  rw [indices_empty, finite_evidence_budget_empty]
#print axioms empty_index_budget_zero

/-- A singleton selection has exactly its unique evidence value as budget. -/
theorem singleton_evidence_budget {Index : Type*} (evidence : Index -> Real)
    (index : Index) :
    finiteEvidenceBudget evidence {index} = evidence index := by
  simp [finiteEvidenceBudget]
#print axioms singleton_evidence_budget

/-- For the identity evidence map, the budget is the ordinary finite sum. -/
theorem identity_evidence_budget (indices : Finset Real) :
    finiteEvidenceBudget id indices = ∑ index ∈ indices, index := by
  rfl
#print axioms identity_evidence_budget

/-- A constant evidence family has budget equal to cardinality times its value. -/
theorem constant_evidence_budget_eq_card_mul {Index : Type*} (value : Real)
    (indices : Finset Index) :
    finiteEvidenceBudget (fun _ => value) indices = (indices.card : Real) * value := by
  simp [finiteEvidenceBudget, nsmul_eq_mul]
#print axioms constant_evidence_budget_eq_card_mul

/-- Equal cardinalities determine the budget when every evidence value is constant. -/
theorem equal_cardinality_determines_constant_budget {Index : Type*} (value : Real)
    (left right : Finset Index) (sameCardinality : left.card = right.card) :
    finiteEvidenceBudget (fun _ => value) left =
      finiteEvidenceBudget (fun _ => value) right := by
  rw [constant_evidence_budget_eq_card_mul, constant_evidence_budget_eq_card_mul,
    sameCardinality]
#print axioms equal_cardinality_determines_constant_budget

/-- The zero evidence family has zero budget for every finite selection. -/
theorem zero_evidence_budget {Index : Type*} (indices : Finset Index) :
    finiteEvidenceBudget (fun _ => (0 : Real)) indices = 0 := by
  simp [finiteEvidenceBudget]
#print axioms zero_evidence_budget

/-- On a singleton index type, every evidence family is cardinality-determined. -/
theorem singleton_index_budget_eq_card_mul (evidence : Unit -> Real)
    (indices : Finset Unit) :
    finiteEvidenceBudget evidence indices = (indices.card : Real) * evidence () := by
  have evidence_constant : evidence = fun _ => evidence () := by
    funext index
    cases index
    rfl
  rw [evidence_constant, constant_evidence_budget_eq_card_mul]
#print axioms singleton_index_budget_eq_card_mul

/-- At exponent negative one, prime evidence is the prime value itself. -/
theorem prime_evidence_negative_one (prime : Nat.Primes) :
    primeEvidence (-1) prime = (prime.1 : Real) := by
  norm_num [primeEvidence, Real.rpow_one]
#print axioms prime_evidence_negative_one

/-- Equal cardinality cannot bound finite prime evidence: even singleton budgets have
arbitrarily large gaps at exponent negative one. -/
theorem equal_cardinality_prime_budget_gap_unbounded (bound : Real) :
    ∃ left right : Finset Nat.Primes,
      left.card = right.card ∧ left.card = 1 ∧
        bound < finiteEvidenceBudget (primeEvidence (-1)) right -
          finiteEvidenceBudget (primeEvidence (-1)) left := by
  obtain ⟨threshold, bound_lt_threshold⟩ := exists_nat_gt (bound + 2)
  obtain ⟨primeValue, threshold_le_prime, primeValue_prime⟩ :=
    Nat.exists_infinite_primes threshold
  let smallPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  let largePrime : Nat.Primes := ⟨primeValue, primeValue_prime⟩
  refine ⟨{smallPrime}, {largePrime}, by simp, by simp, ?_⟩
  rw [singleton_evidence_budget, singleton_evidence_budget,
    prime_evidence_negative_one, prime_evidence_negative_one]
  have threshold_le_prime_real : (threshold : Real) ≤ primeValue := by
    exact_mod_cast threshold_le_prime
  dsimp only [smallPrime, largePrime]
  norm_num only [Nat.cast_ofNat]
  linarith
#print axioms equal_cardinality_prime_budget_gap_unbounded

/-- At exponent zero, every selected prime contributes one, so budget equals cardinality. -/
theorem zero_exponent_prime_budget_eq_card (indices : Finset Nat.Primes) :
    finiteEvidenceBudget (primeEvidence 0) indices = (indices.card : Real) := by
  simp [finiteEvidenceBudget, primeEvidence, nsmul_eq_mul]
#print axioms zero_exponent_prime_budget_eq_card

/-- Thus equal cardinalities do determine zero-exponent prime evidence budgets. -/
theorem equal_cardinality_determines_zero_exponent_prime_budget
    (left right : Finset Nat.Primes) (sameCardinality : left.card = right.card) :
    finiteEvidenceBudget (primeEvidence 0) left =
      finiteEvidenceBudget (primeEvidence 0) right := by
  rw [zero_exponent_prime_budget_eq_card, zero_exponent_prime_budget_eq_card,
    sameCardinality]
#print axioms equal_cardinality_determines_zero_exponent_prime_budget

/-- The equal-cardinality hypothesis is necessary for the nonzero constant contrast. -/
theorem equal_cardinality_hypothesis_is_necessary :
    finiteEvidenceBudget (primeEvidence 0) (∅ : Finset Nat.Primes) ≠
      finiteEvidenceBudget (primeEvidence 0) {⟨2, Nat.prime_two⟩} := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  change finiteEvidenceBudget (primeEvidence 0) ∅ ≠
    finiteEvidenceBudget (primeEvidence 0) {p2}
  rw [zero_exponent_prime_budget_eq_card, zero_exponent_prime_budget_eq_card]
  rw [show ({p2} : Finset Nat.Primes).card = 1 by
    exact Finset.card_singleton p2]
  norm_num
#print axioms equal_cardinality_hypothesis_is_necessary

/- Degeneracy and assumption audit:
   * Empty selections and the empty index type give zero by the first two theorems.
   * Singleton budgets are exact values. They suffice for the core because their gap is
     unbounded, unlike the fixed `{2}` versus `{3}` observation.
   * Constant, zero, identity, and singleton-index families are all checked explicitly.
   * Cardinality zero is the empty-selection case. No separate natural parameter occurs.
   * The core uses primality only via the existence of arbitrarily large primes. Its
     combinatorial mechanism needs cofinally many distinct numeric indices, not prime
     factorization or divisibility.
   * No typeclass instance or algebraic hypothesis is declared. The only theorem hypothesis,
     equal cardinality in the two contrast theorems, is used in each proof and has the named
     concrete counterexample above. -/

end D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceCardinalityBudget
