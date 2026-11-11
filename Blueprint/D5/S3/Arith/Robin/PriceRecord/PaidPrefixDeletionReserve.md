# D5 source compiled; RegUNVALIDATED components

## Abstract

PaidPrefixDeletionReserve

The D5 source target has a current scoped Lean build. Reg mirrors remain unvalidated for kernel/axiom closure, lawful enrollment, source binding and official/RH acceptance; no novelty or consensus claim is asserted. Ordinary Pro reasoning is fallible input. The final uniform paid-prefix repair, its uniform original-price consumer, and the optional elementary-energy consumer remain unfinished. The finite components must not be presented as those final theorems. Existing owners are imported with exact unapplied consumed-helper patches. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.

**Theorem 1.1 (budget prefix deletion reserve).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem budget_prefix_deletion_reserve :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧       ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →       ∀ M : ℕ, (M : ℝ) ≤ C * log X →         ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧           D = Nat.primesLE b.Q \ Nat.primesLE Q ∧ D.card = M ∧           (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧           Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p ∧           (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X)

**Theorem 1.2 (finite prefix deletion cost).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.finite_prefix_deletion_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.finite_prefix_deletion_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem finite_prefix_deletion_cost {X : ℝ} (hX : 4 < X)     (b : Budget) (hb : b.spec X) {Q k M : ℕ}     (hk : 2 ≤ k) (hkp : k.primeFactors = Nat.primesLE Q)     (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) (hQb : Q ≤ b.Q)     (D : Finset ℕ) (hD : D = Nat.primesLE b.Q \ Nat.primesLE Q) (hDM : D.card = M) :     |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| ≤       6 * (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X) + 1) *         ((M : ℝ) * log (2 * X)) / (X ^ 2 * log (X / 2)) ∧     (∀ f : ℝ, (Q : ℝ) ≤ f → f ≤ b.Q →       |log f - log X| ≤ (2 / X) *         (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X)))

**Theorem 1.3 (budget_prefix_deletion_reserve_power).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem budget_prefix_deletion_reserve_power (d : ℕ) :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧       ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →       ∀ M : ℕ, (M : ℝ) ≤ C * log X ^ d →         ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧           D = Nat.primesLE b.Q \ Nat.primesLE Q ∧ D.card = M ∧           (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧           Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p ∧           (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve_power`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.finite_prefix_deletion_cost`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder](ActualRecordAllLogBudgetRemainder.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError](UniformThetaShellError.md)
