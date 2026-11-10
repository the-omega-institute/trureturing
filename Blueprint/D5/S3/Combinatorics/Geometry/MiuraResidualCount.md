# The exact residual split count

## Abstract

Exact normalized height functions are counted with their full extrema and one common side.

Chakshu Gupta, One construction for the Miura-ori flip-graph degree sequence, arXiv:2607.05567v3. The finite height suppliers are adapted from the accompanying CC BY 4.0 Lean source.

**Definition 1.1 (One common boundary side).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.AllOnSide`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraResidualCount.AllOnSide` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

This predicate uses one of four sides and one-based integer coordinates, and asks whether every member lies on that same side.

**Definition 1.2 (The exact residual class).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.Residual`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraResidualCount.Residual` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The class imposes normalization, exact unit-edge increments, exact separate counts of all strict minima and maxima, and the absence of a single common boundary side containing all minima. Individual functions carry no symmetry quotient.

**Theorem 1.3 (Finiteness of the exact residual class).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.residual_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraResidualCount.residual_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The residual class is a subset of the finite set of normalized height functions. The proof supplies finiteness before its cardinality is taken.

**Definition 1.4 (Counting actual normalized functions).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.residualCount`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraResidualCount.residualCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

This is the cardinality of the proved finite residual set. The positivity arguments establish a nonempty rectangle; they impose no extra restriction in the eventual counting region.

**Definition 1.5 (The full polynomial assertion).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.claim`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraResidualCount.claim` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For every natural split a+b=d with d at least five and 1 at most a at most b, one polynomial over the rationals in two variables is chosen before all natural dimensions m,n at least 2d-1. Its total degree is at most d-3, and its evaluations equal the exact residual counts. This definition states the entire assertion and supplies no proof of it.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.AllOnSide`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.Residual`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.residualCount`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResidualCount.residual_finite`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope](MiuraHeightEnvelope.md)
