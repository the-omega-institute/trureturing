# Evidence Budget Is a Sum, Not a Coordinate Count

## Abstract

Finite prime evidence budgets are not controlled by the number of selected primes.

**Definition 1.1 (Finite evidence budget).**

$$B\left(e, J\right) = \sum_{i \in J} e\left(i\right)$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.finiteEvidenceBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The budget of a finite selection is the sum of its evidence values. This named definition is shared by the core and every audit.

**Theorem 1.2 (Empty selections have zero budget).**

$$\forall e, B\left(e, \emptyset\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.finite_evidence_budget_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty finite sum is zero for every index type and evidence family.

**Theorem 1.3 (The empty index type has zero budget).**

$$\forall e: EmptyEvidence, J: EmptyFinsets, B\left(e, J\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.empty_index_budget_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite selection from Empty is empty, so every such budget is zero.

**Theorem 1.4 (A singleton budget is its evidence value).**

$$\forall e, i, B\left(e, \{i\}\right) = e\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.singleton_evidence_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-coordinate selection contributes exactly one summand.

**Theorem 1.5 (Identity evidence gives the ordinary sum).**

$$\forall J, B\left(id, J\right) = \sum_{x \in J} x$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.identity_evidence_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity-map audit reduces the named budget to an ordinary sum.

**Theorem 1.6 (Constant evidence is cardinality times value).**

$$\forall c, J, B\left((i \mapsto c), J\right) = \lvert J \rvert \cdot c$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.constant_evidence_budget_eq_card_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every coordinate has value c, the budget is the set size times c.

**Theorem 1.7 (Cardinality determines every constant budget).**

$$\forall c, J1, J2, \lvert J1 \rvert = \lvert J2 \rvert \Rightarrow B\left((i \mapsto c), J1\right) = B\left((i \mapsto c), J2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_determines_constant_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal cardinalities do determine equal sums under the constant-family restriction. This is the required contrast to the core theorem.

**Theorem 1.8 (Zero evidence has zero budget).**

$$\forall J, B\left((i \mapsto 0), J\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.zero_evidence_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-family specialization is zero for every finite selection.

**Theorem 1.9 (Every Unit-indexed budget is cardinality-determined).**

$$\forall e: UnitEvidence, J: UnitFinsets, B\left(e, J\right) = \lvert J \rvert \cdot e\left(unit\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.singleton_index_budget_eq_card_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every function on Unit is constant, so its budget is size times its unique value.

**Theorem 1.10 (Negative-one evidence is the prime value).**

$$\forall p: Primes, primeEvidence\left(-1, p\right) = p$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.prime_evidence_negative_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent minus one, the imported inverse-power family becomes p.

**Theorem 1.11 (Equal-cardinality prime budgets have unbounded gaps).**

$$\forall M: \mathbb{R}, \exists J1, J2: PrimeFinsets, \lvert J1 \rvert = \lvert J2 \rvert \land \left(\lvert J1 \rvert = 1 \land M < B\left((p \mapsto primeEvidence\left(-1, p\right)), J2\right) - B\left((p \mapsto primeEvidence\left(-1, p\right)), J1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_prime_budget_gap_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real bound, two singleton prime sets have a budget gap above that bound at exponent minus one. Their common cardinality is one.

**Theorem 1.12 (Zero-exponent prime budget equals cardinality).**

$$\forall J: PrimeFinsets, B\left((p \mapsto primeEvidence\left(0, p\right)), J\right) = \lvert J \rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.zero_exponent_prime_budget_eq_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent zero every prime contributes one, so the sum is the size.

**Theorem 1.13 (Cardinality determines zero-exponent prime budgets).**

$$\forall J1, J2: PrimeFinsets, \lvert J1 \rvert = \lvert J2 \rvert \Rightarrow B\left((p \mapsto primeEvidence\left(0, p\right)), J1\right) = B\left((p \mapsto primeEvidence\left(0, p\right)), J2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_determines_zero_exponent_prime_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported prime family itself realizes the constant-family contrast at exponent zero.

**Theorem 1.14 (The equal-cardinality premise is necessary).**

$$B\left((p \mapsto primeEvidence\left(0, p\right)), \emptyset\right) \ne B\left((p \mapsto primeEvidence\left(0, p\right)), \{2\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty prime set and the singleton containing two have unequal zero-exponent budgets. Dropping equal cardinality breaks the contrast.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.constant_evidence_budget_eq_card_mul`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.empty_index_budget_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_determines_constant_budget`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_determines_zero_exponent_prime_budget`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_hypothesis_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.equal_cardinality_prime_budget_gap_unbounded`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.finiteEvidenceBudget`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.finite_evidence_budget_empty`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.identity_evidence_budget`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.prime_evidence_negative_one`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.singleton_evidence_budget`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.singleton_index_budget_eq_card_mul`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.zero_evidence_budget`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceCardinalityBudget.zero_exponent_prime_budget_eq_card`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](PrimeEvidenceSharpThreshold.md)
