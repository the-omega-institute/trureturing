# Exact pointwise extremum correspondence

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Theorem 1.1 (Maxima survive contraction).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLM_of_h_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLM_of_h_max` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

An original ambient strict maximum at the image of a surviving cell is still a strict maximum after signed deletion.

**Theorem 1.2 (Minima survive contraction).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLm_of_h_min`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLm_of_h_min` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The same statement holds for ambient strict minima, including cells adjacent to the deleted column.

**Theorem 1.3 (No maximum is created).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.h_max_of_contractAt_isSLM`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.h_max_of_contractAt_isSLM` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Every contracted strict maximum comes from a strict maximum at the corresponding original surviving cell.

**Theorem 1.4 (No minimum is created).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.h_min_of_contractAt_isSLm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.h_min_of_contractAt_isSLm` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Every contracted strict minimum comes from a strict minimum at the corresponding original surviving cell.

**Theorem 1.5 (Exact pointwise extremum correspondence).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLE_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLE_iff` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

A surviving cell is a contracted strict extremum exactly when its image is an original strict extremum.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLE_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLM_of_h_max`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.contractAt_isSLm_of_h_min`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.h_max_of_contractAt_isSLM`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.h_min_of_contractAt_isSLm`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand](MiuraCoreCellExpand.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraStripRigidity](MiuraStripRigidity.md)
