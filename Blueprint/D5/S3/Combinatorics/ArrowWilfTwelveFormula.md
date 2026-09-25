# Counting the First Arrow-Pattern Avoiders

## Abstract

The first avoidance class is counted by the finite formula F1.

**Definition 1.1 (The largest-fixed-point fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveFormula.twelveFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveFormula.twelveFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For each support value m, the avoiding words whose largest hat-fixed entry is m are equivalent to the disjoint union of TwelveData(n,m,k) over k from zero through n minus m.

**Theorem 1.2 (The first avoidance formula).**

$$\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \operatorname{ncard}\left(\operatorname{avoiders}\left(n, [1, 2], [(3, 3)], 3\right)\right) = \operatorname{F1}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveFormula.card_twelve_avoiders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every positive n, the set cardinality of the first arrow-pattern avoidance class equals F1(n). The no-fixed-point stratum contributes the derangement number; each largest-fixed-point fiber contributes its decorated-object count.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveFormula.card_twelve_avoiders`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveFormula.twelveFiberEquiv`
- Dependency: [D5/S3/Combinatorics/ArrowWilfPartition](ArrowWilfPartition.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfSums](ArrowWilfSums.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveCard](ArrowWilfTwelveCard.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveSurject](ArrowWilfTwelveSurject.md)
