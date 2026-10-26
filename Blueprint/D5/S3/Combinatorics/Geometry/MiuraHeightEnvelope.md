# Finite height envelopes

## Abstract

Finite unit-edge height arrays have attained extremum envelopes and finitely many normalized representatives.

Chakshu Gupta, One construction for the Miura-ori flip-graph degree sequence, arXiv:2607.05567v3. The finite height suppliers are adapted from the accompanying CC BY 4.0 Lean source.

**Definition 1.1 (Unit-edge heights).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsHeight`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsHeight` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

A source cell with one-based coordinates corresponds to its coordinates minus one in Fin m times Fin n. Every actual grid edge has absolute height difference exactly one.

**Definition 1.2 (Strict minima).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsStrictLocalMin`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsStrictLocalMin` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Every existing adjacent cell is one higher. Physical boundary points use all their existing neighbours.

**Definition 1.3 (Strict maxima).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsStrictLocalMax`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsStrictLocalMax` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Every existing adjacent cell is one lower. There is no imposed boundary extension.

**Theorem 1.4 (The attained finite minimum envelope).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.envelope_min`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.envelope_min` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Each value equals the height of some actual strict minimum plus Manhattan distance, and is bounded above by the corresponding cone from every strict minimum. Finiteness supplies descent termination.

**Theorem 1.5 (The attained finite maximum envelope).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.envelope_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.envelope_max` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

Negation gives the dual attained maximum of downward cones. The finite grid remains the same actual height array.

**Theorem 1.6 (Finitely many normalized heights).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.CanonicalHeights_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.CanonicalHeights_finite` (`✓ std3`). ∎

*Citation.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

On a nonempty rectangle normalization at the origin and the unit-edge bound put every integer value in a fixed finite interval. The resulting finite product contains all normalized height functions.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.CanonicalHeights_finite`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsHeight`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsStrictLocalMax`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.IsStrictLocalMin`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.envelope_max`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.envelope_min`
