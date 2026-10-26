# Unit edges survive deletion

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Definition 1.1 (The actual signed slope).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The slope is the row-zero height difference between the frozen column and its left neighbour.

**Theorem 1.2 (Slope transport to every row).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope_eq` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For a unit-edge height function, this same signed slope equals that horizontal difference in every row.

**Theorem 1.3 (The slope is a unit sign).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope_pm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope_pm` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The actual frozen slope is either one or negative one.

**Definition 1.4 (Signed deletion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.contractAt`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreContract.contractAt` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Delete one internal frozen column and subtract its uniform signed slope from every column to its right.

**Theorem 1.5 (Unit edges survive deletion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.contractAt_isHeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreContract.contractAt_isHeight` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For every pair of adjacent surviving grid cells, the contracted height difference has absolute value one, including the new seam.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.contractAt`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.contractAt_isHeight`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope_eq`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreContract.frozenSlope_pm`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope](MiuraCoreFrozenSlope.md)
