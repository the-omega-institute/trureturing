# Arrow Patterns and Their Avoidance Classes

## Abstract

Arrow-pattern containment combines an ordered subsequence with prescribed arrows in the inverse Foata cycle map.

**Definition 1.1 (Left-to-right maxima).**

$$\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \operatorname{IsLtrMax}\left(p, i\right) \Leftrightarrow \left(\forall j \in \mathrm{Nat},\; j < i \Rightarrow \operatorname{getD}\left(p, j, 0\right) < \operatorname{getD}\left(p, i, 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ArrowWilfDefs.IsLtrMax` (`✓ std3`).

*Citation.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

An entry at index i is a left-to-right maximum when it exceeds every entry at an earlier index. Indices start at zero, and getD returns zero outside the list.

**Definition 1.2 (The inverse Foata cycle map).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfDefs.hat`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfDefs.hat` (`✓ std3`).

*Citation.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Find the index of x in p. If the next entry exists and is not a left-to-right maximum, map x to that entry. Otherwise map x to the last left-to-right maximum at or before its index. Thus each block cut before a left-to-right maximum becomes a cycle.

**Definition 1.3 (Containment of an arrow pattern).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfDefs.Contains`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfDefs.Contains` (`✓ std3`).

*Citation.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Contains nu H k p holds when a function x selects increasing values x(1) through x(k) from p, the list obtained by mapping nu through x is a sublist of p, and hat p maps x(b) to x(c) for every pair (b,c) in H.

**Definition 1.4 (The avoidance class).**

$$\forall n \in \mathrm{Nat},\; \forall nu \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall H \in \operatorname{List}\left(\operatorname{Pair}\left(\mathrm{Nat}, \mathrm{Nat}\right)\right),\; \forall k \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; p \in \operatorname{avoiders}\left(n, nu, H, k\right) \Leftrightarrow \left(\operatorname{Perm}\left(p, List.range'(1, n)\right) \land \left(\neg \operatorname{Contains}\left(nu, H, k, p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ArrowWilfDefs.avoiders` (`✓ std3`).

*Citation.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The class consists of lists permuting the natural numbers from one through n that do not contain the specified arrow pattern.

**Definition 1.5 (Equality of the two avoidance counts).**

$$claim \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \operatorname{ncard}\left(\operatorname{avoiders}\left(n, [1, 2], [(3, 3)], 3\right)\right) = \operatorname{ncard}\left(\operatorname{avoiders}\left(n, [2, 3], [(1, 1)], 3\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ArrowWilfDefs.claim` (`✓ std3`).

*Citation.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every positive n, the avoidance classes of (12; 3 to 3) and (23; 1 to 1) have equal set cardinality.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfDefs.Contains`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfDefs.IsLtrMax`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfDefs.hat`
