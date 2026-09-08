# Positive Gramian Balancing

## Abstract

Positive definite Gramians produce mutually inverse balancing coordinates and an exact Gramian-product spectrum.

**Definition 1.1 (Balancing output).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates`

*Formalization.* `D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output certificate contains the coordinate matrices, positive weights, both inverse identities and both Gramian congruences. Its inhabitation is proved from positive definiteness below.

**Definition 1.2 (Positive square root).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot`

*Formalization.* `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Uses Mathlib's positive continuous-functional-calculus square root.

**Theorem 1.3 (Root properties).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives positive definiteness, self-adjointness and the exact square identity for the constructed root.

**Theorem 1.4 (Construction of balancing coordinates).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonalizes sqrt(P) Q sqrt(P) using Mathlib's spectral theorem, rescales by fourth roots, and proves both inverse identities and simultaneous congruences. No balancing matrix is an input. This construction is noncomputable and permits repeated eigenvalues.

**Definition 1.5 (Chosen constructed coordinates).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates`

*Formalization.* `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Selects the output of the proved existence construction. This is an exact mathematical construction, not a floating-point eigensolver.

## References

- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot_spec`
