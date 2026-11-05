# Finite frozen-cut suppliers

## Abstract

Boundary occupancy and uniform actual cuts around an extrema-free row.

The finite walk and frozen-column proofs are adapted from Chakshu Gupta's accompanying CC BY 4.0 Lean source at commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11. They are applied to the transposed original array. Full license terms and attribution accompany the source.

**Theorem 1.1 (Physical boundary rows contain extrema).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.boundary_rows_occupied`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.boundary_rows_occupied` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Every unit-edge integer height array with at least two rows and one column has an ambient minimum or maximum on each physical boundary row. The finite boundary-walk result is applied to the same transposed array.

**Theorem 1.2 (Uniform cuts at an actual unoccupied row).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.inactive_row_uniform_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.inactive_row_uniform_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For every unit-edge integer array with at least one column, an internal row containing no ambient extremum has one common downward unit increment on both incident full-width cuts. The increment is either one or minus one. The finite extrema-free walk result first makes the two neighbours symmetric, and the frozen-column slope result makes the sign constant across all columns.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.boundary_rows_occupied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.inactive_row_uniform_cuts`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
