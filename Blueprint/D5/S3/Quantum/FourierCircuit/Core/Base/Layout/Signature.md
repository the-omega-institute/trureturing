# Core Base Layout Signature

## Abstract

Addressed quantum circuit: Core Base Layout Signature

**Definition 1.1 (QuantumSignature).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.QuantumSignature`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.QuantumSignature` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Ordered positive dimensions, independent of physical wire identities.

**Definition 1.2 (Basis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.Basis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.Basis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Computational-basis labels retain one value for every system.

**Definition 1.3 (register).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.register`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.register` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The register determined by the ordered physical dimensions.

**Definition 1.4 (qubits).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.qubits`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.qubits` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A signature of exactly the stated number of dimension-two systems.

**Definition 1.5 (qubitsIndexEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.qubitsIndexEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.qubitsIndexEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Fixed big-endian coordinates for a qubit signature.

**Definition 1.6 (Placement).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.Placement`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.Placement` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A placement for exactly these dimensions; identity injectivity comes from the layout itself.

**Definition 1.7 (indexEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.indexEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.indexEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Transport each local value by its certified dimension equality. Physical placement does not permit a caller-selected permutation of basis values.

**Definition 1.8 (place).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.place`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.place` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Place the signature on any injective assignment of physical identities.

**Definition 1.9 (canonicalPlacement).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.canonicalPlacement`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.canonicalPlacement` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Canonical local placement uses each argument's position as its identity.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.Basis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.Placement`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.QuantumSignature`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.canonicalPlacement`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.indexEquiv`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.place`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.qubits`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.qubitsIndexEquiv`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature.register`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum](Quantum.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](../../../Util/FinPow/BinaryBasis.md)
