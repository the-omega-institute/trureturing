# Core Base Layout Quantum Relabeling

## Abstract

Addressed quantum circuit: Core Base Layout Quantum Relabeling

For every injective physical map from Nat to Nat, QuantumAlg.QuantumWire.relabel changes each wire identity by that map and preserves its dimension. QuantumAlg.QuantumLayout.relabel applies the same map to every wire and proves identity injectivity by composition; every original logical position and basis value is retained.

**Definition 1.1 (relabelBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling.relabelBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling.relabelBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Logical basis values retain the same finite dimension at every original position.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling.relabelBasis`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum](../Quantum.md)
