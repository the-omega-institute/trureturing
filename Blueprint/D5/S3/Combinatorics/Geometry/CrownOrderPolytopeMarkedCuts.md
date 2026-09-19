# Marked cuts and parity profiles

## Abstract

Marked cycle partitions yield exact parity-profile cardinalities.

The first count agrees with the denominator-cleared form of source Lemma 3.5 on its stated range. The formal proof also covers m equals zero and all vanishing support cases. The other statements justify the actual block and parity bookkeeping.

**Theorem 1.1 (The marked parity-profile count).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.card_prescribedOddConnectedCyclePartition_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.card_prescribedOddConnectedCyclePartition_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two and i at least two, multiplying the number of connected partitions of the 2n-cycle into i blocks with 2m odd blocks by i gives 2n times choose(i,2m) times choose(n+m-1,i-1). The factor i counts markings; all natural support cases are included.

**Theorem 1.2 (The number of odd blocks is even).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.actualOddCycleBlocks_card_even`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.actualOddCycleBlocks_card_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

In every connected partition of a nonzero cycle of even size, the number of actual odd-cardinality blocks is even. This is the parity constraint needed to index profiles by 2m.

**Theorem 1.3 (Cuts count the actual quotient blocks).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.quotient_card_eq_boundaryCuts_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.quotient_card_eq_boundaryCuts_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For a cycle of size at least three with at least two boundary cuts, the actual quotient cardinality equals the cardinality of the boundary-cut set.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.actualOddCycleBlocks_card_even`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.card_prescribedOddConnectedCyclePartition_identity`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.quotient_card_eq_boundaryCuts_card`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions](CrownOrderPolytopeCyclePartitions.md)
