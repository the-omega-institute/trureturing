# A Ramsey obstruction to simultaneous switch maxima

## Abstract

Four coordinate triples of one colour force a missed fixed-pair switch maximum.

**Theorem 1.1 (A fixed finite binary fibre fails on some power).**

Lean statement: `D5/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction.noCommonMaximumInSomePower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction.noCommonMaximumInSomePower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Fix a nontrivial finite centreless Steiner loop and a finite nontrivial binary fibre. Some positive coordinatewise power of the loop has the following property. For every normalized label table there are distinct nonidentity pivots and a second label table that gives more successful starts at the two zero lifts. One table therefore cannot attain all individual fixed-pair maxima.

Choose one nonidentity element and put it in each pair of coordinate positions to obtain an edge point. The three edge points of each coordinate triple form an original block. Finite Ramsey gives four coordinates whose four face blocks all carry the same label. These blocks form an alternating square with opposite pivots and zero return. Prescribing nonzero returns on every component away from the identity retains the old successful starts and adds a start from this square.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction.noCommonMaximumInSomePower`
- Dependency: [D5/S3/Combinatorics/GroupWords/NathansonProblem9](../../GroupWords/NathansonProblem9.md)
- Dependency: [D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschSwitchCount](SteinerPaschSwitchCount.md)
