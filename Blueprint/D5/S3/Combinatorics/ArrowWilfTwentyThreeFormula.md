# Counting the Second Arrow-Pattern Avoiders

## Abstract

The second avoidance class is counted by the finite formula F2.

**Definition 1.1 (Avoiders as words on the standard support).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula.avoiderWordEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula.avoiderWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For each n, the set of lists avoiding (23; 1 to 1) is equivalent to the subtype of words on the support from one through n that do not contain this pattern.

**Theorem 1.2 (The second avoidance formula).**

$$\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \operatorname{ncard}\left(\operatorname{avoiders}\left(n, [2, 3], [(1, 1)], 3\right)\right) = \operatorname{F2}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula.card_twentyThree_avoiders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every positive n, the set cardinality of the second arrow-pattern avoidance class equals F2(n). The no-fixed-point stratum, the stratum fixed only at n, and the smaller-minimum fibers give its three terms.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula.avoiderWordEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula.card_twentyThree_avoiders`
- Dependency: [D5/S3/Combinatorics/ArrowWilfPartition](ArrowWilfPartition.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfSums](ArrowWilfSums.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse](ArrowWilfTwentyThreeInverse.md)
