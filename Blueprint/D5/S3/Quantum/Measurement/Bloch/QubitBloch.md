# Qubit Bloch coordinates

## Abstract

Generic qubit Bloch coordinates and scalar effects.

**Definition 1.1 (B).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(a\right) = ((((a\left(0\right): \mathbb{C})) \cdot (pauliMatrix\left(\operatorname{Pauli.X}\right))) + (((a\left(1\right): \mathbb{C})) \cdot (pauliMatrix\left(\operatorname{Pauli.Y}\right)))) + (((a\left(2\right): \mathbb{C})) \cdot (pauliMatrix\left(\operatorname{Pauli.Z}\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/Bloch/QubitBloch.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real coordinates multiply the three single-qubit Pauli matrices.

**Theorem 1.2 (The Pauli coordinate matrix).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(a\right) = \begin{pmatrix}(a\left(2\right): \mathbb{C})&((a\left(0\right): \mathbb{C})) - ((\operatorname{Complex.I}) \cdot ((a\left(1\right): \mathbb{C})))\\((a\left(0\right): \mathbb{C})) + ((\operatorname{Complex.I}) \cdot ((a\left(1\right): \mathbb{C})))&-(a\left(2\right): \mathbb{C})\end{pmatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Bloch/QubitBloch.B_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pauli expansion gives the four complex matrix entries.

**Definition 1.3 (scalarB).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{scalarB}\left(t, a\right) = (((t: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))) + (\operatorname{B}\left(a\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/Bloch/QubitBloch.scalarB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real scalar identity is added to the traceless Bloch matrix.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/QubitBloch.B`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/QubitBloch.B_formula`
- Truth anchor: `D5/S3/Quantum/Measurement/Bloch/QubitBloch.scalarB`
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../../Information/Pauli/PauliMatrix.md)
