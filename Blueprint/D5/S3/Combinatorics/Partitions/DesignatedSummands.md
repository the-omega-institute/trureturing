# Ordered tuples with designated summands

## Abstract

The coefficient of the Euler quotient counts ordered tuples with an actual designated occurrence.

For each distinct part size of multiplicity m, a marked partition carries a choice in Fin m. An ordered tuple uses a degree assignment on the component positions with total degree n. A component of degree zero is the empty partition. The local multiplicity series is 1 plus the sum of m times q to the power im for positive m, where i is the part size. Multiplying its Euler denominators gives the factor in degree 6i. Taking the product over all part sizes yields the quotient F, and coefficient convolution gives the ordered tuple count.

**Definition 1.1 (MarkedPartition).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.MarkedPartition`

*Formalization.* `D5/S3/Combinatorics/Partitions/DesignatedSummands.MarkedPartition` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

A partition of n together with one choice of actual occurrence for each part size present.

**Definition 1.2 (MarkedTuple).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.MarkedTuple`

*Formalization.* `D5/S3/Combinatorics/Partitions/DesignatedSummands.MarkedTuple` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

An ordered tuple of k marked partitions with total size n. Each position may have degree zero.

**Definition 1.3 (markedCount).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedCount`

*Formalization.* `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedCount` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The cardinality of the type of ordered marked tuples.

**Definition 1.4 (markedPartitionFintype).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedPartitionFintype`

*Formalization.* `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedPartitionFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The type of markings of partitions of a fixed size is finite.

**Definition 1.5 (markedTupleFintype).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedTupleFintype`

*Formalization.* `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedTupleFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

There are finitely many ordered marked tuples at fixed component count and total size.

**Definition 1.6 (F).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.F`

*Formalization.* `D5/S3/Combinatorics/Partitions/DesignatedSummands.F` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The Euler quotient f6 divided by f1 f2 f3 as a formal power series.

**Theorem 1.7 (F_const).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.F_const`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/DesignatedSummands.F_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The Euler quotient has constant coefficient one.

**Theorem 1.8 (marked_count_coeff).**

Lean statement: `D5/S3/Combinatorics/Partitions/DesignatedSummands.marked_count_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/DesignatedSummands.marked_count_coeff` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

For all natural k and n, the integer cast of the tuple count equals the coefficient of degree n in F raised to k.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.F`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.F_const`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.MarkedPartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.MarkedTuple`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedPartitionFintype`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.markedTupleFintype`
- Truth anchor: `D5/S3/Combinatorics/Partitions/DesignatedSummands.marked_count_coeff`
- Dependency: [D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct](../PowerSeries/DilatedEulerProduct.md)
