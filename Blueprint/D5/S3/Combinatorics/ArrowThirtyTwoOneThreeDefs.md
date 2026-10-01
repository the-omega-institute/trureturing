# The (32; 1 to 3) Avoidance Series

## Abstract

The avoidance numbers and their ordinary generating series are defined for the arrow pattern (32; 1 to 3).

**Definition 1.1 (Avoidance numbers).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.count`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The number at n is the cardinality of the permutations of 1 through n avoiding (32; 1 to 3).

**Definition 1.2 (Ordinary generating series).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.series`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.series` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The coefficient of x to the n in this integer power series is the avoidance number at n.

**Definition 1.3 (Cubic equation and distinguished branch).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.claim`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The avoidance series F satisfies 1 + (3x - 2)F + (1 - x)(1 - 2x)F squared + x cubed F cubed = 0. Any integer formal power series G satisfying the same equation, with constant coefficient one and coefficient of x equal to one, equals F.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.count`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs.series`
- Dependency: [D5/S3/Combinatorics/ArrowWilfDefs](ArrowWilfDefs.md)
