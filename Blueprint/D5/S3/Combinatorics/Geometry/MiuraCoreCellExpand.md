# Seam differences preserve signs

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Definition 1.1 (The surviving-cell injection).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The map embeds the smaller physical rectangle in the original rectangle by skipping exactly the deleted internal column.

**Theorem 1.2 (No surviving cells are identified).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand_injective` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The surviving-cell map is injective on the actual rectangular cell type.

**Theorem 1.3 (Every surviving cell is represented).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand_surjOn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand_surjOn` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Every original cell outside the deleted column is the image of one cell of the smaller rectangle.

**Theorem 1.4 (The origin stays normalized).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.contractAt_isCanonicalHeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.contractAt_isCanonicalHeight` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

A normalized unit-edge height function remains normalized after signed deletion because the origin lies strictly before the removed internal column.

**Theorem 1.5 (Seam differences preserve signs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.contractAt_diff_seam_LtoR`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.contractAt_diff_seam_LtoR` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Across the new seam the contracted height difference equals the corresponding original incident difference, using the uniform frozen slope.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand_injective`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.cellExpand_surjOn`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.contractAt_diff_seam_LtoR`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.contractAt_isCanonicalHeight`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreContract](MiuraCoreContract.md)
