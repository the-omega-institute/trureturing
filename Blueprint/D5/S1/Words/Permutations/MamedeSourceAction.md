# Source Excursion and Target Factorization

## Abstract

The first-orientation excursion determines the target endpoint and word support.

Let gamma be the product of the deleted excursion and let pi=sigma gamma inverse. The source word used below is an actual singleton reduced word with the first-orientation shape, not merely an arbitrary factorization of sigma.

**Theorem 1.1 (Action of the deleted excursion).**

$$1 \le m < i < M \le n \land 1 \le t \le n + 1 \implies \operatorname {gamma}\left(\operatorname {position}\left(n, t\right)\right) = \operatorname {position}\left(n, \operatorname {cycleCase}\left(m, i, M + 1, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeSourceAction.deletedExcursion_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Here gamma is the product of Deleted(m,M,i). The cycleCase map sends m to i, i to M+1, and M+1 to m, and fixes every other one-based position. The bounds keep these positions distinct.

**Theorem 1.2 (Source and image products).**

$$1 \le m < i \le j < M \le n \land \forall k \in q , i < k < M \implies \operatorname {prod}\left(n, \operatorname {concat}\left(p, \operatorname {Full}\left(m, M, i, j\right), q\right)\right) = \operatorname {prod}\left(n, \operatorname {Image}\left(i, j, p, q\right)\right) \times \operatorname {prod}\left(n, \operatorname {Deleted}\left(m, M, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeSourceAction.source_full_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The suffix support makes every generator of q commute with the deleted excursion. Splitting the first descent then gives the product identity for any prefix p, without assuming an actual source word or its SourceShape premise.

**Theorem 1.3 (Every target singleton factors).**

$$\operatorname {ExactSource}\left(n, m, M, i, j, sigma\right) \land \operatorname {SourceShape}\left(m, M, i, j, a0, p0, q0\right) \land \operatorname {Singleton}\left(n, sigma, a0\right) \implies \forall b , \operatorname {Singleton}\left(n, pi, b\right) \implies \exists p , \exists q , b = \operatorname {Image}\left(i, j, p, q\right) \land \operatorname {PrefixBounds}\left(m, j, p\right) \land \operatorname {SuffixBounds}\left(i, M, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeSourceAction.source_target_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Here pi=sigma gamma inverse. Every singleton reduced target word contains the full descent from j to i; every prefix letter lies strictly between m and j, and every suffix letter strictly between i and M. The source-shape and singleton premises remain live.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeSourceAction.deletedExcursion_action`
- Truth anchor: `D5/S1/Words/Permutations/MamedeSourceAction.source_full_product`
- Truth anchor: `D5/S1/Words/Permutations/MamedeSourceAction.source_target_factorization`
- Dependency: [D5/S1/Words/Permutations/MamedeCrossing](MamedeCrossing.md)
