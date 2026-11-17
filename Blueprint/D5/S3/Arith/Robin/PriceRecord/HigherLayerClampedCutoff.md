# Constructed strict cutoff with the lower boundary retained

## Abstract

Constructed strict cutoff with the lower boundary retained.

The cutoff is constructed by the intermediate value theorem when eta<beta_j(2), and otherwise equals 2. Occupancy is eta<beta_j(u) iff u<cutoff, including u=2 and zero-margin roots. Both prices remain positive for 0<s<=1/2. Integrated slope and log((1+s)/(1-s))<=3s give movement<=9s x_minus/j. For every active layer and X>=exp(2), the actual lower-price root is <=(2jX)^(1/j)<=2X^(1/j), and j<6 log X. The finite active-layer cardinality and the sum x_minus/j<37 sqrt(X) are proved uniformly in all j. Integer counting uses only the finite set minimum and maximum and Nat.card_Icc, giving length+1, with no estimate of prime density or prime gaps.

**Theorem 1.1 (root exists).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.root_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.root_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem root_exists {j : ℕ} (hj : 2 ≤ j) {η : ℝ} (hη : 0 < η) (hactive : η < beta j 2) : ∃ u : ℝ, 2 < u ∧ beta j u = η

**Theorem 1.2 (cutoff spec).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem cutoff_spec {j : ℕ} (hj : 2 ≤ j) {η : ℝ} (hη : 0 < η) : 2 ≤ cutoff j η ∧ beta j (cutoff j η) ≤ η ∧ (2 < cutoff j η → beta j (cutoff j η) = η) ∧ (η < beta j 2 ↔ 2 < cutoff j η)

**Theorem 1.3 (cutoff antitone).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem cutoff_antitone {j : ℕ} (hj : 2 ≤ j) {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) : cutoff j ζ ≤ cutoff j η

**Theorem 1.4 (cutoff occupancy).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_occupancy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_occupancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem cutoff_occupancy {j : ℕ} (hj : 2 ≤ j) {η u : ℝ} (hη : 0 < η) (hu : 2 ≤ u) : η < beta j u ↔ u < cutoff j η

**Theorem 1.5 (log price ratio le).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_price_ratio_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_price_ratio_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem log_price_ratio_le {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) : log ((1 + s) / (1 - s)) ≤ 3 * s

**Theorem 1.6 (cutoff movement).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_movement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_movement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem cutoff_movement {j : ℕ} (hj : 2 ≤ j) {«λ» s : ℝ} («hλ» : 0 < «λ») (hs : 0 < s) (hs2 : s ≤ 1 / 2) : cutoff j ((1 - s) * «λ») - cutoff j ((1 + s) * «λ») ≤ 9 * s * cutoff j ((1 - s) * «λ») / j

**Theorem 1.7 (two mul index le two pow).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.two_mul_index_le_two_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.two_mul_index_le_two_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem two_mul_index_le_two_pow {j : ℕ} (hj : 2 ≤ j) : 2 * j ≤ 2 ^ j

**Theorem 1.8 (active root bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_root_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_root_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem active_root_bounds {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) {j : ℕ} (hj : 2 ≤ j) (hactive : 2 < cutoff j ((1 - s) / (X * log X))) : cutoff j ((1 - s) / (X * log X)) ≤ (2 * j * X) ^ (1 / (j : ℝ)) ∧ (2 * j * X) ^ (1 / (j : ℝ)) ≤ 2 * X ^ (1 / (j : ℝ)) ∧ (j : ℝ) < 6 * log X

**Theorem 1.9 (log cuberoot lt three sqrt).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_cuberoot_lt_three_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_cuberoot_lt_three_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem log_cuberoot_lt_three_sqrt {X : ℝ} (hX : exp 2 ≤ X) : log X * X ^ (1 / 3 : ℝ) < 3 * sqrt X

**Theorem 1.10 (integer interval card).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.integer_interval_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.integer_interval_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem integer_interval_card (S : Finset ℕ) {a b : ℝ} (hab : a ≤ b) (hS : ∀ p ∈ S, a ≤ (p : ℝ) ∧ (p : ℝ) < b) : (S.card : ℝ) ≤ b - a + 1

**Theorem 1.11 (active layer card).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_layer_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_layer_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem active_layer_card {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) (J : Finset ℕ) (hJ : ∀ j ∈ J, 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X))) : (J.card : ℝ) ≤ 6 * log X

**Theorem 1.12 (active cutoff sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_cutoff_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_cutoff_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem active_cutoff_sum {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) (J : Finset ℕ) (hJ : ∀ j ∈ J, 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X))) : (∑ j ∈ J, cutoff j ((1 - s) / (X * log X)) / j) < 37 * sqrt X

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_cutoff_sum`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_layer_card`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_root_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_antitone`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_movement`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_occupancy`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_spec`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.integer_interval_card`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_cuberoot_lt_three_sqrt`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_price_ratio_le`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.root_exists`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.two_mul_index_le_two_pow`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope](HigherLayerLogSlope.md)
