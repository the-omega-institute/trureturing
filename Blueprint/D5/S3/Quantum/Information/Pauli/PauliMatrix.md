# Pauli matrices

## Abstract

The single-qubit Pauli labels and matrix representation.

**Definition 1.1 (Pauli labels).**

$$\operatorname{Pauli} = \left\{\operatorname{I}, \operatorname{X}, \operatorname{Y}, \operatorname{Z}\right\}$$

*Formalization.* `D5/S3/Quantum/Information/Pauli/PauliMatrix.Pauli` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

The four single-qubit Pauli labels.

**Definition 1.2 (Pauli matrices).**

$$\left(\operatorname{pauliMatrix}\left(\operatorname{I}\right) = 1 \land \operatorname{pauliMatrix}\left(\operatorname{X}\right) = \operatorname{qubitX}\right) \land \left(\operatorname{pauliMatrix}\left(\operatorname{Y}\right) = i \cdot (\operatorname{qubitX} \cdot \operatorname{qubitZ}) \land \operatorname{pauliMatrix}\left(\operatorname{Z}\right) = \operatorname{qubitZ}\right)$$

*Formalization.* `D5/S3/Quantum/Information/Pauli/PauliMatrix.pauliMatrix` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

The label I gives the identity, X and Z give the frozen Pauli matrices qubitX and qubitZ, and Y gives i X Z, where i is the imaginary unit, so that Y has rows (0, -i) and (i, 0).

## References

- Truth anchor: `D5/S3/Quantum/Information/Pauli/PauliMatrix.Pauli`
- Truth anchor: `D5/S3/Quantum/Information/Pauli/PauliMatrix.pauliMatrix`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../../FiniteDimensional.md)
