# Fixed-layer source components

## Abstract

FixedLayerShrinkingPrimeRoster

The module supplies fixed-layer asymptotic and shrinking-roster components. These components do not establish the final uniform paid-prefix repair, its uniform original-price consumer or an elementary-energy consumer. Reg audit incomplete: faithful full-telescope typed Reg attempts are present; lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain unfinished.

**Theorem 1.1 (root_ratio).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem root_ratio {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => cutoff j (referencePrice X) / X ^ ((j : ℝ)⁻¹))       atTop (𝓝 ((j : ℝ) ^ ((j : ℝ)⁻¹)))

**Theorem 1.2 (root_atTop).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem root_atTop {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => cutoff j (referencePrice X)) atTop atTop

**Theorem 1.3 (root_log_ratio).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_log_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_log_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem root_log_ratio {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => log (cutoff j (referencePrice X)) / log X)       atTop (𝓝 ((j : ℝ)⁻¹))

**Theorem 1.4 (fixed_layer_shrinking_prime_roster_power).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem fixed_layer_shrinking_prime_roster_power {j : ℕ} (hj : 2 ≤ j)     (w d : ℕ) (hw : 0 < w) :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ X : ℝ, T ≤ X →       ∃ S : Finset ℕ,         C * log X ^ d ≤ (S.card : ℝ) ∧         (∀ p ∈ S, p.Prime ∧ cutoff j (referencePrice X) < (p : ℝ) ∧           (p : ℝ) ≤ cutoff j (referencePrice X) * (1 + 1 / log X ^ w)) ∧         cutoff j (referencePrice X) / (2 * log X ^ w) ≤           ∑ p ∈ S, log p

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster_power`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_atTop`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_log_ratio`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_ratio`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic](FixedLayerRootAsymptotic.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
