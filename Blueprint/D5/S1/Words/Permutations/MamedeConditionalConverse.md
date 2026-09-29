# Conditional Deletion Converse

## Abstract

A first-orientation source singleton makes excursion deletion surjective onto target singletons.

Fix 1<=m<i<=j<M<=n and the endpoint, exterior fixed-point, and non-oscillating-source conditions of ExactSource. Suppose in addition that a0 is an actual singleton reduced word for sigma and has SourceShape(m,M,i,j,a0,p0,q0). Let gamma be the product of Deleted(m,M,i), and put pi=sigma gamma inverse.

**Theorem 1.1 (Every target singleton lifts).**

$$\operatorname {ExactSource}\left(n, m, M, i, j, sigma\right) \land \operatorname {SourceShape}\left(m, M, i, j, a0, p0, q0\right) \land \operatorname {Singleton}\left(n, sigma, a0\right) \implies \forall b , \operatorname {Singleton}\left(n, pi, b\right) \implies \exists a , \exists p , \exists q , \operatorname {Singleton}\left(n, sigma, a\right) \land \operatorname {SourceShape}\left(m, M, i, j, a, p, q\right) \land \operatorname {Image}\left(i, j, p, q\right) = b \land \operatorname {length}\left(b\right) < \operatorname {length}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeConditionalConverse.source_deletion_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

For every singleton reduced word b of pi, there are p and q with all letters of p in (m,j) and of q in (i,M). The word a=p ++ Full(m,M,i,j) ++ q is a singleton reduced word for sigma. Its deletion image is exactly b and b is strictly shorter than a. The theorem does not derive the SourceShape premise from ExactSource, and it makes no reflected-orientation, cardinality, oscillation, or induction assertion.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeConditionalConverse.source_deletion_surjective`
- Dependency: [D5/S1/Words/Permutations/MamedeSourceAction](MamedeSourceAction.md)
