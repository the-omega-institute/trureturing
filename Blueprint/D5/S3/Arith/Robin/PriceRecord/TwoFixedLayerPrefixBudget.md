# D5 and Reg sources compile; RegUNVALIDATED audit

## Abstract

TwoFixedLayerPrefixBudget

The 2/3 ledger specializes the new arbitrary-layer construction and has no D5 proof consumer. The live 2/4 repair uses two_roster_integer_ledger_at_layers at 2,4. The seeded 2/3 coefficient endpoint and finite paid comparison remain separate substantive results.

The D5 and Reg source targets compile under the scoped Lean checks. The retained Reg sources compile with standard axiom closure; the escape audit remains incomplete for lawful enrollment and source binding; no novelty or consensus claim is asserted. Ordinary Pro reasoning is fallible input. These components feed the separate actual two/four paid-prefix repair. The uniform original-price and optional elementary-energy endgoals remain open. Existing owners are imported with visibility-only consumed-helper exposures. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.

**Theorem 1.1 (seeded two layer coefficients).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.seeded_two_layer_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.seeded_two_layer_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem seeded_two_layer_coefficients :     ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∃ C T : ℝ, 0 < C ∧ 1 < T ∧       ∀ X : ℝ, T ≤ X → ∀ δ₀ f : ℝ,         0 ≤ δ₀ → δ₀ ≤ log (2 * X) → f ∈ Set.Icc (X / 2) (2 * X) →         ∃ a b : ℕ, b ≤ B ∧ (a + b : ℝ) ≤ C * log X ∧           log X - log 2 ≤ δ₀ + log f ∧           δ₀ + log f ≤ 2 * log X + 2 * log 2 ∧           δ₀ + log f - ε / 2 ≤             (a : ℝ) * (2 * log (cutoff 2 (referencePrice X)) - log X) +             (b : ℝ) * (3 * log (cutoff 3 (referencePrice X)) - log X) ∧           (a : ℝ) * (2 * log (cutoff 2 (referencePrice X)) - log X) +             (b : ℝ) * (3 * log (cutoff 3 (referencePrice X)) - log X) ≤               δ₀ + log f - ε / 4

**Theorem 1.2 (two roster integer ledger).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem two_roster_integer_ledger {X : ℝ} (hX : 4 < X) {Q : ℕ}     (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))     {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     (hsupport : ∀ p : ℕ, p.Prime →       2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)     (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)     (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = 1)     (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = 2) :     let n := strictInteger (referencePrice X)     let base := higherCore n * prefixInteger Q     let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧       (∀ p : ℕ, k.factorization p =         base.factorization p + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧       log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       log (higherCore k : ℝ) = log (higherCore n : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       actualDefect X k - completeFirstLayerLoss X k =         (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p 2) * log p) +         (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p 3) * log p) ∧       (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ j : ℕ, 2 ≤ j →         (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p))

**Theorem 1.3 (finite paid prefix comparison).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.finite_paid_prefix_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.finite_paid_prefix_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem finite_paid_prefix_comparison {η X μ : ℝ} (hX : 4 < X)     {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)     (hrecord : ∀ a : ℕ, 0 < a → a < m →       goldenResourceObjective μ a < goldenResourceObjective μ m)     (hclock : X = log (m : ℝ))     (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))     (b : Budget) (hb : b.spec X)     (hslack : 0 ≤ X - log (k : ℝ))     (hpaid : |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +       (actualDefect X k - completeFirstLayerLoss X k) +         referencePrice X * (X - log (k : ℝ)) ≤ η / (X * log X)) :     k ≤ m ∧ 0 ≤ actualDefect X m - completeFirstLayerLoss X m ∧       actualDefect X m - completeFirstLayerLoss X m + μ * (X - log (k : ℝ)) ≤         η / (X * log X) +         6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *           |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /             (X ^ 2 * log (X / 2))

**Theorem 1.4 (residual nonneg).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.residual_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.residual_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem residual_nonneg {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n) :     0 ≤ actualDefect X n - completeFirstLayerLoss X n

**Theorem 1.5 (insert roster at prefix).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster_at_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster_at_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem insert_roster_at_prefix {X : ℝ} (hX : 4 < X) {base Q : ℕ}     (hb2 : 2 ≤ base) (hpref : base.primeFactors = Nat.primesLE Q)     (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) {r : ℝ}     (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     {J : ℕ} (hJ : 1 ≤ J) (A : Finset ℕ)     (hA : ∀ p ∈ A, p.Prime ∧ p ≤ Q ∧ base.factorization p = J - 1) :     let k := base * ∏ p ∈ A, p     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧       log (k : ℝ) - log (base : ℝ) = ∑ p ∈ A, log p ∧       (∀ p, k.factorization p = base.factorization p + if p ∈ A then 1 else 0) ∧       actualDefect X k - completeFirstLayerLoss X k =         (actualDefect X base - completeFirstLayerLoss X base) +           ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p

**Theorem 1.6 (two price compare).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem two_price_compare {X μ : ℝ} {m k : ℕ}     (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)     (hrecord : ∀ a : ℕ, 0 < a → a < m →       goldenResourceObjective μ a < goldenResourceObjective μ m)     (hclock : X = log (m : ℝ)) (hslack : 0 ≤ X - log (k : ℝ)) :     k ≤ m ∧ actualDefect X m - actualDefect X k ≤       (referencePrice X - μ) * (X - log (k : ℝ))

**Theorem 1.7 (prefix budget integer).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_budget_integer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_budget_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem prefix_budget_integer {n Q : ℕ} (hQ : 2 ≤ Q)     (hsupport : ∀ p : ℕ, p.Prime → 2 ≤ n.factorization p → p ≤ Q) :     let k := higherCore n * prefixInteger Q     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧     log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) ∧     ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →       (j ≤ k.factorization p ↔ j ≤ n.factorization p)

**Theorem 1.8 (two_roster_integer_ledger_at_layers).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger_at_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger_at_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem two_roster_integer_ledger_at_layers {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)     {X : ℝ} (hX : 4 < X) {Q : ℕ}     (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))     {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     (hsupport : ∀ p : ℕ, p.Prime →       2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)     (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)     (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = i - 1)     (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = j - 1) :     let n := strictInteger (referencePrice X)     let base := higherCore n * prefixInteger Q     let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧       (∀ p : ℕ, k.factorization p =         base.factorization p + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧       log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       log (higherCore k : ℝ) = log (higherCore n : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       actualDefect X k - completeFirstLayerLoss X k =         (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p i) * log p) +         (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p j) * log p) ∧       (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ l : ℕ, 2 ≤ l →         (l ≤ k.factorization p ↔ l ≤ optimalLayerCount (referencePrice X) p))

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster_at_prefix`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.residual_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_budget_integer`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.finite_paid_prefix_comparison`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.seeded_two_layer_coefficients`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger_at_layers`
- Dependency: [D5/S3/Arith/DiophantineApproximation/StablePositiveSemigroup](../../DiophantineApproximation/StablePositiveSemigroup.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair](ActualHigherLayerBudgetRepair.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic](FixedLayerRootAsymptotic.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster](FixedLayerShrinkingPrimeRoster.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret](HigherLayerInsertionRegret.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve](PaidPrefixDeletionReserve.md)
- Dependency: [D5/S3/Constants/Irrationality/LogPrimeRatioIrrationality](../../../Constants/Irrationality/LogPrimeRatioIrrationality.md)
