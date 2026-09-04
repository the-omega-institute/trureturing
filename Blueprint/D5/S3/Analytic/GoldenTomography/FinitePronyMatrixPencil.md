# Finite Prony Matrix Pencil

## Abstract

For separated active modes, the consecutive finite Hankel pencil is similar to diagonal modal transport and identifies the Prony spectrum.

**Theorem 1.1 (The Vandermonde observation map intertwines modal transport).**

$$\operatorname{V}(x)^{T}\cdot\operatorname{T}(x) = \operatorname{D}(x)\cdot\operatorname{V}(x)^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.finite_prony_modal_transport_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct Prony nodes, the square Vandermonde observation matrix is nonsingular. The canonical observed transport is obtained by conjugating diagonal multiplication by the nodes through this observation map.

The displayed intertwining identity is the finite change-of-coordinates bridge between hidden spectral fibers and observed Hankel coordinates.

**Theorem 1.2 (The consecutive Hankel pencil equals observed modal transport).**

$$\operatorname{P}(x, w) = \operatorname{T}(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.finite_prony_matrix_pencil_eq_modal_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the nodes are distinct and every modal weight is nonzero, the zero-shift square Hankel section is nonsingular. Its inverse multiplied by the one-shift section equals the canonical observed modal transport.

This is the exact noiseless matrix-pencil identity. It does not select eigenvectors numerically or quantify sensitivity to perturbations.

**Theorem 1.3 (The Hankel pencil characteristic polynomial is the Prony annihilator).**

$$\operatorname{charpoly}(\operatorname{P}(x, w)) = \operatorname{A}(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.finite_prony_matrix_pencil_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix pencil is similar to the diagonal matrix of Prony nodes. Characteristic-polynomial invariance under this conjugation gives the product of X - q_j, exactly the reciprocal Prony annihilator.

Thus the exact finite Hankel pencil identifies the indexed modal nodes with multiplicity. No noisy root perturbation, confluent-mode recovery, or infinite-dimensional Koopman claim is made.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.finite_prony_matrix_pencil_charpoly`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.finite_prony_matrix_pencil_eq_modal_transport`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil.finite_prony_modal_transport_intertwining`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport](FinitePronyShiftedHankelTransport.md)
