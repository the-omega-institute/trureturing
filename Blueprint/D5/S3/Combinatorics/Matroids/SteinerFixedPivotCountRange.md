# Fixed-Pair Steiner Switch Counts

## Abstract

The full range of binary switch counts at a fixed pair of Steiner pivots.

**Theorem 1.1 (Each selected four-point component contributes four full fibres).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange.labelledFixedPivotCountRange`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange.labelledFixedPivotCountRange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Take a finite Steiner loop with trivial centre, two distinct nonidentity pivots, the graph of their left translations, and a finite binary vector space A. Let b count quotient vertices failing to return after two rounds of the pivot composite. Let s count four-point components other than the component containing the identity.

Among normalized binary extensions and their compatible labelled complete triple systems, the attainable counts are exactly |A|(b+4k), for 0≤k≤s. When A is trivial, only k=0 is available. The deletion and retained pivot have labels (p,0) and (q,0), and the matching is the actual matching of uncovered pairs.

A four-point component closes in two rounds of the composite. Its lift contributes either no starts or the full fibre at each of the four vertices. The identity component always returns with zero shift. A nonzero fibre element can be assigned to any selected set of the remaining square components using the single-pair return theorem. For any given labelling, the return is constant on a component. Counting the disjoint full fibres gives the converse.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange.labelledFixedPivotCountRange`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSwitchSupport](SteinerSwitchSupport.md)
