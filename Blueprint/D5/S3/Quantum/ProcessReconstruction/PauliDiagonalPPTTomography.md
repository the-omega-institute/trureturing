# Pauli-diagonal PPT probes for process tomography

## Abstract

Sharp worst-direction conditioning for process tomography with four-dimensional Pauli-diagonal PPT probes.

**Theorem 1.1 (PPT conditioning upper bound).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.two_qubit_diagonal_gain_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.two_qubit_diagonal_gain_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gurvir Singh (2026). *Ancilla Assisted Quantum Process Tomography using Bound entangled states*. URL: <https://arxiv.org/abs/2605.19182v3>.

*Commentary.*

Each party consists of two qubits. Pair an anticommuting Pauli pair and its Hermitian product with their transposes on the other party. The two commuting paired observables give four nonnegative joint projection expectations on the density matrix. Partial transpose supplies the four complementary sign patterns. The sum of the three absolute coefficients is at most one, so the least singular value is at most one twelfth.

**Theorem 1.2 (An attaining PPT probe).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.sixBellWitness_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.sixBellWitness_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gurvir Singh (2026). *Ancilla Assisted Quantum Process Tomography using Bound entangled states*. URL: <https://arxiv.org/abs/2605.19182v3>.

*Commentary.*

The witness has six equally weighted tensor Bell states. Its partial transpose also has six eigenvalues one sixth and ten zeros. The identity coefficient gives singular value one fourth and every other Pauli coefficient gives one twelfth. The witness is the published six-Bell probe, locally unitarily equivalent to the lattice state of Benatti, Floreanini and Piani.

**Theorem 1.3 (Actual channels attain the weakest direction).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.d4_cptp_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.d4_cptp_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gurvir Singh (2026). *Ancilla Assisted Quantum Process Tomography using Bound entangled states*. URL: <https://arxiv.org/abs/2605.19182v3>.

*Commentary.*

For each diagonal probe, two distinct completely positive trace-preserving channels with qubit output attain the coefficient of least absolute value. The squared output Hilbert–Schmidt distance equals the squared least gain times the squared distance between their unnormalized Choi matrices.

**Theorem 1.4 (Uniform gain of the attaining probe).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.sixBellWitness_hsSquare_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.sixBellWitness_hsSquare_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gurvir Singh (2026). *Ancilla Assisted Quantum Process Tomography using Bound entangled states*. URL: <https://arxiv.org/abs/2605.19182v3>.

*Commentary.*

For the six-Bell probe, the squared output Hilbert–Schmidt norm of any linear channel difference is at least one over one hundred forty-four times the squared Hilbert–Schmidt norm of its unnormalized Choi matrix. Together with the class upper bound and the channel pair, this yields the sharp worst-direction gain of one twelfth.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.d4_cptp_attains`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.sixBellWitness_attains`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.sixBellWitness_hsSquare_lower`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.two_qubit_diagonal_gain_le`
- Dependency: [D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation](../Information/EntanglementDistanceBellDiagonalRefutation.md)
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Information/Pauli/PauliMatrix.md)
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../Matrix/PartialTransposeTrace.md)
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](../Recovery/ActualChannelAlgebra.md)
