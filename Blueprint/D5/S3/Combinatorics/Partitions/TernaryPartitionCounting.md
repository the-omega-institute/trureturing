# Ternary partition transport and four-party counting

## Abstract

Surjective mergers transport arbitrary weighted ternary partition sums, yielding the four-party coefficient cancellation for every sign-representative family.

The structural counting proof uses TernaryPartitionOrbit to classify nonzero anchored ternary colourings modulo sign. A merger is any surjection between anchored label sets; its source anchor need not map to its target anchor. Factorization through its fibres, followed by subtracting the target-anchor colour, gives precisely the compatible source partitions. The merger sum therefore counts each compatible equality partition once.

Akella and Gadde, arXiv:2610.27080v1, Section II Eqs. (7)–(9) and Appendix A, give an odd-replica rank formula whose n=3 specialization also implies the four-party entropy collapse. Restoring n^{−(q−2)}, explicitly omitted at their Eq. (2), gives the normalization used by StabilizerMultiEntropyCollapse. This is a structural formal proof and reusable library for an existing conclusion, with no new unique-solve or global-priority claim. The counting question in arXiv:2607.06050v2 Section 6 is historical source text.

**Definition 1.1 (The equality partition of an anchored mode).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.partition`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.partition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The setoid kernel of the zero-anchored ternary colouring on Option α.

**Definition 1.2 (Pulling a target partition back through a merger).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.pullPartition`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.pullPartition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The kernel of the anchored target colouring composed with the merger map.

**Definition 1.3 (The four-label separation matrix).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.cutPattern`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.cutPattern` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The Boolean entry at i,j records whether the two ternary colours differ.

**Definition 1.4 (Coordinate colours with the last label anchored at zero).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.colourValue`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.colourValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For q labels, coordinates Fin(q−1) carry the ternary mode values and the last label has colour zero.

**Definition 1.5 (The six pair mergers).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.pairMergers`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.pairMergers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The six surjections merge AB, AC, AD, BC, BD and CD respectively.

**Definition 1.6 (The four singleton cuts).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.singletonCuts`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.singletonCuts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The four surjections split ABC:D, ABD:C, ACD:B and BCD:A respectively.

**Definition 1.7 (The three balanced cuts).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.balancedCuts`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.balancedCuts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The three surjections split AB:CD, AC:BD and AD:BC respectively.

**Definition 1.8 (Weighted separation matrices at normalized arity).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.partitionSumR`

*Formalization.* `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.partitionSumR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For r free coordinates, sum an arbitrary real weight of each induced four-label separation matrix over the chosen finite representative family and merger into r+1 labels.

**Theorem 1.9 (Transport through arbitrary surjective mergers).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.merger_sum_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.merger_sum_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For arbitrary index types α and β, choose finite sets Pα and Pβ excluding zero and containing exactly one of u and −u for each nonzero mode. For every surjection m : Option α → Option β and every weight f into an additive commutative monoid, summing f over pulled-back target representatives equals its sum over source representative partitions containing ker(m). There is no finiteness assumption on the index types themselves and no condition m(none)=none. Injectivity uses sign-representative uniqueness; surjectivity uses quotient factorization and reanchoring. This theorem is consumed by the encoding bridge in result.

**Theorem 1.10 (Arbitrary-weight four-party ternary counting).**

Lean statement: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

For any opposite-pair representative families in arities three, two and one and any real weight on the four-by-four Boolean separation matrix, the full sum minus the six pair-merger sums plus twice the four singleton-cut sums plus the three balanced-cut sums is zero. A finite catalogue covers all fifteen four-label equivalence relations. At each nonconstant ternary partition, the coefficients cancel; the discrete partition cannot occur because four labels use only three colours, and excluding zero removes the indiscrete partition. The finite catalogue normalizes only these four-point coefficients; it is not a general Möbius formula or a Coxeter identification. Arbitrary weighted mode sums are connected to those coefficients by merger_sum_transport. StabilizerMultiEntropyCollapse.partition_count applies this result to its original thirteen, four and one concrete representatives, and the existing rank and entropy tail then gives the n=3 four-party relation. Other replica counts and party counts are outside this conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.balancedCuts`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.colourValue`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.cutPattern`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.merger_sum_transport`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.pairMergers`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.partition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.partitionSumR`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.pullPartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.singletonCuts`
- Dependency: [D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit](TernaryPartitionOrbit.md)
