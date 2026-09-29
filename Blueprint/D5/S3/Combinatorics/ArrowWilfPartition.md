# Partitions by Extremal Fixed Points

## Abstract

Avoiding words partition according to whether a fixed point exists and, if so, its largest or smallest value.

**Definition 1.1 (Words satisfying a predicate).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.Avoiding`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.Avoiding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Avoiding(s,P) is the subtype of words on s satisfying P.

**Definition 1.2 (The largest-fixed-point fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.MaxFixedFiber`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.MaxFixedFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word in this fiber satisfies P, fixes m under hat, and fixes no value of s larger than m.

**Definition 1.3 (The smallest-fixed-point fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.MinFixedFiber`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.MinFixedFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word in this fiber satisfies P, fixes m under hat, and fixes no value of s smaller than m.

**Definition 1.4 (Map to the largest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.maxFixedPartitionMap`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.maxFixedPartitionMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The map sends an avoiding word either to the no-fixed-point case or to the fiber indexed by its largest hat-fixed value.

**Definition 1.5 (Partition by largest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.maxFixedPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.maxFixedPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When all no-fixed-point words satisfy P, avoiding words are equivalent to the sum of NoFixed(s) and all largest-fixed-point fibers.

**Definition 1.6 (Map to the smallest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.minFixedPartitionMap`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.minFixedPartitionMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The map sends an avoiding word either to the no-fixed-point case or to the fiber indexed by its smallest hat-fixed value.

**Definition 1.7 (Partition by smallest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfPartition.minFixedPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfPartition.minFixedPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When all no-fixed-point words satisfy P, avoiding words are equivalent to the sum of NoFixed(s) and all smallest-fixed-point fibers.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.Avoiding`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.MaxFixedFiber`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.MinFixedFiber`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.maxFixedPartitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.maxFixedPartitionMap`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.minFixedPartitionEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfPartition.minFixedPartitionMap`
- Dependency: [D5/S3/Combinatorics/ArrowWilfCountingCore](ArrowWilfCountingCore.md)
