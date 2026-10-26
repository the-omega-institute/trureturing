# Uniform side difference

## Abstract

Finite signed contraction on the actual rectangular height grid.

**Definition 1.1 (Aligned walk extrema).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.alignedExt`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.alignedExt` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

An aligned row records two equal side signs and the corresponding existing vertical signs of a strict extremum.

**Theorem 1.2 (Downward propagation).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.cascade_down`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.cascade_down` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

A row with aligned side signs and a vertical step preventing an extremum propagates to the bottom endpoint, where extremum-freeness gives a contradiction.

**Theorem 1.3 (Upward propagation).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.cascade_up`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.cascade_up` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The analogous propagation toward the top endpoint also contradicts extremum-freeness.

**Theorem 1.4 (Opposite side signs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.extremumFree_rainbow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.extremumFree_rainbow` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For three compatible unit-step walks with no aligned extremum, the two horizontal side differences sum to zero at every row.

**Theorem 1.5 (Uniform side difference).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.rainbow_dL_const`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.rainbow_dL_const` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

If the two side differences sum to zero at every row and all three walks have unit increments, each adjacent pair of rows has the same left difference.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.alignedExt`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.cascade_down`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.cascade_up`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.extremumFree_rainbow`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.rainbow_dL_const`
