# The q11 inventory

## Abstract

The exact strict and weak inventories at the first eleven-layer price.

All p and k binders range over all natural numbers. Prime is Nat.Prime. The imported goldenLayerMarginal(p,k) is log((1-(1/p)^(k+1))/(1-(1/p)^k))/log(p). optimalLayerCount counts every strictly profitable positive prime layer, and weakLayerCount includes equality. strictInteger and maximalInteger are the actual imported strict-count integer and full weak-layer product, with their original total definitions. No optimizer domain is replaced by a finite menu.

**Definition 1.1 (q11).**

$$q11 = \operatorname{goldenLayerMarginal}\left(11, 1\right)$$

*Formalization.* `D5/S3/Arith/Robin/Activation5040Inventory.q11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is exactly log(12/11)/log(11), which is positive. The proof establishes 1/28 < q11 < 1/25 using exact rational powers and real-log order.

**Definition 1.2 (The strict exponents).**

$$\forall p \in \mathbb{N},\; \operatorname{targetExponent5040}\left(p\right) = \left(\operatorname{if} \left(p = 2\right) \operatorname{then} 4 \operatorname{else} \left(\operatorname{if} \left(p = 3\right) \operatorname{then} 2 \operatorname{else} \left(\operatorname{if} \left(p = 5\right) \operatorname{then} 1 \operatorname{else} \left(\operatorname{if} \left(p = 7\right) \operatorname{then} 1 \operatorname{else} 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/Activation5040Inventory.targetExponent5040` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The piecewise function is defined on every natural p; it is the factorization of 5040, including zero and one directions.

**Definition 1.3 (The weak exponents).**

$$\forall p \in \mathbb{N},\; \operatorname{targetExponent55440}\left(p\right) = \left(\operatorname{if} \left(p = 11\right) \operatorname{then} 1 \operatorname{else} \operatorname{targetExponent5040}\left(p\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/Activation5040Inventory.targetExponent55440` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first eleven-layer is the only additional layer.

**Theorem 1.4 (Every strict count).**

$$\forall p \in \mathbb{N},\; \operatorname{optimalLayerCount}\left(q11, p\right) = \operatorname{targetExponent5040}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.optimalLayerCount_q11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuse: golden_resource_unique_optimum at 1/25, optimal_layer_count_spec, positive_layers_eq_count_interval, golden_layer_marginal_le_inv_pow and golden_layer_strict_decrease. Selected final layers are transported from 1/25. Exact power-28 comparisons exclude the next 2,3,5,7 layers. For every prime p at least 13, inverse/log bounds strictly exclude the first layer, then strict decrease excludes every higher layer. The threshold architecture and log-comparison proof adapt the private layer_threshold_separation_5040 proof in GoldenResource5040PriceInterval; private declarations are not imported as public API. Nonprime counts and target exponents are both proved zero.

**Theorem 1.5 (Every weak count).**

$$\forall p \in \mathbb{N},\; \operatorname{weakLayerCount}\left(q11, p\right) = \operatorname{targetExponent55440}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.weakLayerCount_q11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual weak prefix-count API includes the first eleven-layer at equality and excludes every higher eleven-layer by strict decrease. Nonprime directions, including p=0 and p=1, have count zero.

**Theorem 1.6 (The actual strict integer).**

$$\operatorname{strictInteger}\left(q11\right) = 5040$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.strictInteger_q11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factorization injectivity identifies the actual strictInteger from its public strictInteger_counts API and the all-direction count theorem. This asserts an actual integer equality.

**Theorem 1.7 (The actual maximal integer).**

$$\operatorname{maximalInteger}\left(q11\right) = 55440$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.maximalInteger_q11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factorization injectivity and maximalInteger_spec identify the full weak-layer product: 2^4 * 3^2 * 5 * 7 * 11 = 55440.

**Theorem 1.8 (All strict layers).**

$$\forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le k \Rightarrow \left(q11 < \operatorname{goldenLayerMarginal}\left(p, k\right) \Leftrightarrow k \le \operatorname{targetExponent5040}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.q11_strict_layer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime and every positive layer, exact set membership and the proved count equality give both implications.

**Theorem 1.9 (All weak layers).**

$$\forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le k \Rightarrow \left(q11 \le \operatorname{goldenLayerMarginal}\left(p, k\right) \Leftrightarrow k \le \operatorname{targetExponent55440}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.q11_weak_layer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This quantifies over the same unrestricted prime and positive layer domain and includes every equality layer.

**Theorem 1.10 (The complete equality tie).**

$$\forall p \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le k \Rightarrow \left(\operatorname{goldenLayerMarginal}\left(p, k\right) = q11 \Leftrightarrow \left(p = 11 \land k = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Activation5040Inventory.q11_equality_layer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weak membership and failure of strict membership force exactly p=11,k=1. This is the complete equality classification, without a tie-free hypothesis. The bounded Robin application belongs to the separate reuse task. All-price EndpointRobinEstimates, NPC7 signed floor and global coverage remain open; no complete Robin or RH assertion follows here.

## References

- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.maximalInteger_q11`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.optimalLayerCount_q11`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.q11`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.q11_equality_layer_iff`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.q11_strict_layer_iff`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.q11_weak_layer_iff`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.strictInteger_q11`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.targetExponent5040`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.targetExponent55440`
- Truth anchor: `D5/S3/Arith/Robin/Activation5040Inventory.weakLayerCount_q11`
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](ActualTwoPriceDefect.md)
