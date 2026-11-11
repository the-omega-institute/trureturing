# Finite first-layer block coercivity

## Abstract

ActualFirstLayerBlockCoercivity

Finite theta-mass lower bounds for the complete first-layer arithmetic loss on missing and occupied prime blocks. The whole theorem telescopes below retain the prime-prefix support, endpoint and log-budget conditions. The D5 source target compiles under the scoped Lean check; the escape audit remains RegUNVALIDATED under issue 28966.

**Theorem 1.1 (mem_block).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.mem_block`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.mem_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate statement: theorem mem_block {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {p : ℕ} :     p ∈ block a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b

**Theorem 1.2 (first_margin).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.first_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.first_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate statement: theorem first_margin {X : ℝ} {p : ℕ} (hp : p.Prime) :     rawLayerMargin X p 1 = log (1 + 1 / (p : ℝ)) - log p / (X * log X)

**Theorem 1.3 (positive_margin_mem).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.positive_margin_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.positive_margin_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate statement: theorem positive_margin_mem {X : ℝ} (hX : 1 < X) (m : ℕ)     {p : ℕ} (hp : p.Prime) (hg : 0 < rawLayerMargin X p 1) :     p ∈ lossPrimes X m

**Theorem 1.4 (missing_block_theta_lower_bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate statement: theorem missing_block_theta_lower_bound {X a b : ℝ} {m Q : ℕ}     (hX : 4 < X) (_hm : 2 ≤ m) (hsupport : m.primeFactors = Nat.primesLE Q)     (ha : 1 < a) (hab : a < b) (hQa : (Q : ℝ) ≤ a) (hbX : b + 1 / 2 < X) :     (X - b - 1 / 2) * (Chebyshev.theta b - Chebyshev.theta a) /       (X * (b + 1 / 2) * log b) ≤ completeFirstLayerLoss X m

**Theorem 1.5 (occupied_block_theta_lower_bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate statement: theorem occupied_block_theta_lower_bound {X a b : ℝ} {m Q : ℕ}     (hX : 4 < X) (_hm : 2 ≤ m) (hsupport : m.primeFactors = Nat.primesLE Q)     (ha : 1 < a) (hab : a < b) (hbQ : b ≤ (Q : ℝ)) (hXa : X < a) :     (a - X) * (Chebyshev.theta b - Chebyshev.theta a) /       (X * a * log b) ≤ completeFirstLayerLoss X m

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.first_margin`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.mem_block`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.positive_margin_mem`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual](ActualRecordHigherLayerResidual.md)
