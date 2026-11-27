# A forced final pair in a normalized Pfaffian

## Abstract

A zero penultimate upper column forces a final pair in the normalized Pfaffian over any commutative ring.

**Definition 1.1 (Prefix inclusion).**

Lean statement: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.embed`

*Formalization.* `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, embed sends i in Fin(2n) to the index of the same value in Fin(2(n+1)).

**Definition 1.2 (Penultimate index).**

Lean statement: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.last0`

*Formalization.* `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.last0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, last0(n) is the index of value 2n in Fin(2(n+1)).

**Definition 1.3 (Last index).**

Lean statement: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.last1`

*Formalization.* `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.last1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, last1(n) is the index of value 2n+1 in Fin(2(n+1)).

**Theorem 1.4 (Forced final pair).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot \left(n + 1\right)\right), \operatorname{Fin}\left(2 \cdot \left(n + 1\right)\right), R\right),\; \left(\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; A\left(\operatorname{embed}\left(i\right), \operatorname{last0}\left(n\right)\right) = 0\right) \Rightarrow \operatorname{pfaffian}\left(A\right) = \operatorname{pfaffian}\left(\operatorname{submatrix}\left(A, embed, embed\right)\right) \cdot A\left(\operatorname{last0}\left(n\right), \operatorname{last1}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.pfaffian_forced_last_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be any commutative ring and A any matrix on Fin(2(n+1)), for n a natural number. For every earlier index i in Fin(2n), assume A(embed(i),last0(n))=0. Every nonzero normalized listing term must pair last0(n) with last1(n). The surviving listings are precisely the extensions of normalized prefix listings, with the final pair appended. The extension preserves the permutation sign, and the added factor is A(last0(n),last1(n)). Summing gives the equality, including n=0. The Pfaffian here is the repository's normalized pair-listing sum, and no skew-symmetry hypothesis is required.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.embed`
- Truth anchor: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.last0`
- Truth anchor: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.last1`
- Truth anchor: `D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.pfaffian_forced_last_pair`
- Dependency: [D5/S0/Certificates/Combinatorics/NormalizedPfaffian](NormalizedPfaffian.md)
