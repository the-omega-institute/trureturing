# Core Base Classical Value

## Abstract

Addressed quantum circuit: Core Base Classical Value

**Definition 1.1 (Value).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Value.Value`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Value.Value` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Nominal runtime encodings carried by the closed storage shapes. Every constructor fixes its CShape index, so equal-width unsigned, signed, residue, unit-residue, bit-vector, and fixed-vector values remain distinct types. Residue and elliptic-curve constructors are raw encodings only: their modulus, unit, curve, and validity proofs belong to later semantic carriers.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Value.Value`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/Shape](../Accounting/Shape.md)
