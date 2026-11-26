# A Pasch-count bound for simultaneous switch maxima

## Abstract

A bound on the number of Pasches guarantees a common maximum for all pivot pairs.

**Theorem 1.1 (One table attains every fixed-pair maximum).**

Lean statement: `D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschThreshold.common_maximum_of_pasch_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschThreshold.common_maximum_of_pasch_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the original finite Steiner loop have trivial centre and let the finite binary fibre have dimension d at least three. Count each Pasch once as an unordered set of four original blocks. If this count is at most 2^(d+1)−1, there is one normalized label table whose successful-start count at the two zero lifts is at least that of every competing table, for each ordered pair of distinct nonidentity pivots.

Every alternating square away from the identity has a return vector with four nonzero block coordinates. A maximal subspace disjoint from the forbidden vectors has every nonzero quotient point represented by a forbidden vector. When the forbidden family meets the bound exactly, adjoining zero cannot give a subspace. Any four-dimensional binary subspace of such a set would have total nonzero weight sixty, whereas each coordinate contributes zero or eight. Two forbidden vectors therefore have a nonzero sum outside the family. Quotienting by its line identifies them and leaves all forbidden images nonzero. The strict counting bound then supplies an avoiding kernel of codimension at most d.

Embedding the quotient into the fibre gives one table with nonzero return at every square away from the identity. Under every table, longer alternating components contribute all their starts and the identity component contributes none. The resulting table attains all individual maxima.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschThreshold.common_maximum_of_pasch_count`
- Dependency: [D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschSwitchCount](SteinerPaschSwitchCount.md)
