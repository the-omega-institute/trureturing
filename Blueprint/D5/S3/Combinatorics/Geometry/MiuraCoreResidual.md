# The exact residual class is preserved

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Definition 1.1 (One physical side).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.cellOnSide`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.cellOnSide` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Side membership uses the actual first or last row or column of the finite rectangle.

**Theorem 1.2 (Boundary membership survives deletion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.cellExpand_on_side`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.cellExpand_on_side` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For each of the four sides separately, a surviving cell lies on that side before deletion exactly when it lies on the corresponding physical side afterward.

**Theorem 1.3 (The source common-side condition).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.all_minima_side_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.all_minima_side_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The one-based source predicate that every minimum lies on one specified side agrees with pointwise physical side membership of all strict minima.

**Theorem 1.4 (The number of minima is unchanged).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_minima_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_minima_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Signed internal frozen deletion preserves the exact cardinality of the set of strict minima.

**Theorem 1.5 (The number of maxima is unchanged).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_maxima_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_maxima_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Signed internal frozen deletion separately preserves the exact cardinality of the set of strict maxima.

**Theorem 1.6 (The same side contains all minima).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_all_minima_side_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_all_minima_side_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For each specified physical side, all minima lie on that side before signed deletion exactly when all contracted minima lie on the corresponding side.

**Theorem 1.7 (The exact residual class is preserved).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For every split a,b and every actual normalized residual height array, deleting an internal frozen column preserves normalization, both exact extremum counts, and the absence of one common side containing all minima.

**Theorem 1.8 (Delete inside an oversized frozen run).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.residual_width_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.residual_width_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For every nonempty row axis and at least two columns, a residual height array of split a,b with width greater than 2(a+b)-1 has two consecutive genuinely frozen columns. One can delete the first with its actual uniform signed slope and retain exactly the original residual class. The existence argument counts the occupied columns and maximal unoccupied runs in this same array; if no two unoccupied columns were consecutive, every unoccupied column would start a run, contradicting the width bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.all_minima_side_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.cellExpand_on_side`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.cellOnSide`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_all_minima_side_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_maxima_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_minima_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.contractAt_residual`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreResidual.residual_width_reduction`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreBoundary](MiuraCoreBoundary.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreExtremum](MiuraCoreExtremum.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraResidualCount](MiuraResidualCount.md)
