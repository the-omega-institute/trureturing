# Fusion State Cardinality

## Abstract

Surjective component maps and an injective product map bound the number of fused states.

**Theorem 1.1 (Fusion state cardinality has component and product bounds).**

$$\forall Y, Z_{1}, Z_{2}, Z_{12},\ [\operatorname{Finite} Y] [\operatorname{Finite} Z_{1}] [\operatorname{Finite} Z_{2}] [\operatorname{Finite} Z_{12}],\ pi: Y \to Z_{12}, toFirst: Z_{12} \to Z_{1}, toSecond: Z_{12} \to Z_{2}, intoProduct: Z_{12} \to Z_{1} \times Z_{2},\ \operatorname{Surjective}\left(pi\right) \Rightarrow \operatorname{Surjective}\left(toFirst\right) \Rightarrow \operatorname{Surjective}\left(toSecond\right) \Rightarrow \operatorname{Injective}\left(intoProduct\right) \Rightarrow\ (\max(\operatorname{card}(Z_{1}), \operatorname{card}(Z_{2})) \leq \operatorname{card}(Z_{12}) \land \operatorname{card}(Z_{12}) \leq \min(\operatorname{card}(Y), \operatorname{card}(Z_{1}) \times \operatorname{card}(Z_{2}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FusionStateCardinality.fusion_state_cardinality_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y, Z1, Z2, and Z12 be finite state types. Suppose Y maps surjectively onto the fused type Z12, Z12 maps surjectively onto each component type, and Z12 maps injectively into the product Z1 times Z2. Then the fused cardinality is at least both component cardinalities and at most both the original cardinality and the product cardinality.

Pinned Mathlib supplies the exact four ingredients: Nat.card_le_card_of_surjective for the two lower comparisons and the original-state upper comparison, Nat.card_le_card_of_injective for the product upper comparison, and Nat.card_prod to evaluate the product type. Loogle and LeanSearch returned those component results and nearby range lemmas, but no theorem packaging the complete maximum/minimum bound.

The theorem records exactly the finite cardinal consequence of the canonical quotient and product maps. It makes no independence, product-surjectivity, entropy, metric, or asymptotic claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FusionStateCardinality.fusion_state_cardinality_bounds`
