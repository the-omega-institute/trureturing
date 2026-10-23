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

**Theorem 1.4 (Inverse diagonal square-root scalings).**

$$\forall (iota: \operatorname{Type}), [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)], \forall (w: iota \to \mathbb{R}), (\forall (i: iota), 0 < w\left(i\right)) \Rightarrow \operatorname{let} D=\operatorname{diagonal}\left(w\right), \operatorname{let} H=\operatorname{diagonal}\left(\lambda (i: iota), \operatorname{Real.sqrt}\left(w\left(i\right)\right)\right), \operatorname{let} I=\operatorname{diagonal}\left(\lambda (i: iota), (\operatorname{Real.sqrt}\left(w\left(i\right)\right))^{-1}\right), (H \cdot I = 1) \land ((I \cdot H = 1) \land ((I \cdot D \cdot I = 1) \land (I \cdot \operatorname{diagonal}\left(\lambda (i: iota), w\left(i\right)^{2}\right) \cdot I = D)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/PositiveGramianBalancing.diagonal_scalings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive weights w on any finite index type, let D be diagonal(w), H be diagonal(sqrt(w)), and I be diagonal(1/sqrt(w)). Then H I = I H = I D I = 1, and I diagonal(w squared) I = D. These four identities give the inverse coordinate changes and the rescaled Gramian congruences.

**Theorem 1.5 (Construction of balancing coordinates).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonalizes sqrt(P) Q sqrt(P) using Mathlib's spectral theorem, rescales by fourth roots, and proves both inverse identities and simultaneous congruences. No balancing matrix is an input. This construction is noncomputable and permits repeated eigenvalues.

**Definition 1.6 (Chosen constructed coordinates).**

Lean statement: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates`

*Formalization.* `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Selects the output of the proved existence construction. This is an exact mathematical construction, not a floating-point eigensolver.

## References

- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.diagonal_scalings`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot`
- Truth anchor: `D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot_spec`
