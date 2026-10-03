# Complete Mappings on an Even Product

## Abstract

An explicit complete mapping on ZMod 2 times ZMod (2m) for every positive m.

Let H_m be the additive group ZMod 2 times ZMod (2m), with m positive. A complete mapping is a function theta on H_m for which theta and x mapped to x + theta(x) are both bijective. Its graph consequently selects every row, column and sum symbol of the addition table once.

**Definition 1.1 (The explicit map).**

$$\operatorname{theta}\left(m, epsilon, j\right) = (epsilon + \operatorname{h}\left(m, k\right), k)$$

*Formalization.* `D5/S3/Factorization/CompleteMappingEvenProduct.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here k = j + epsilon.val in ZMod (2m), and h_m(k) is zero in ZMod 2 when k.val < m and one otherwise. epsilon.val is the standard representative zero or one.

**Theorem 1.2 (Both projected maps are permutations).**

$$\forall m \in \mathbb{N}, 0 < m \implies \operatorname{Bijective}\left(\operatorname{theta}\left(m\right)\right) \land \operatorname{Bijective}\left(x \mapsto x + \operatorname{theta}\left(m, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CompleteMappingEvenProduct.theta_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first map is injective by recovering k and then epsilon. For the sum map, reduction modulo two recovers epsilon; doubling determines k modulo m, while h_m(k) selects its lower or upper lift in ZMod (2m). Both finite self-maps are therefore bijective. This proves only this explicit family, not a classification of complete mappings on all finite groups.

## References

- Truth anchor: `D5/S3/Factorization/CompleteMappingEvenProduct.theta`
- Truth anchor: `D5/S3/Factorization/CompleteMappingEvenProduct.theta_complete`
