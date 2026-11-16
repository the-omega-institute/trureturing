# Entries of the original full QFT word

## Abstract

Entries of the original full QFT word

**Theorem 1.1 (Full-word Fourier entry).**

$$\forall oracles \in \mathit{OracleModel},\; \forall q \in \mathit{Nat},\; \forall environment \in \operatorname{Interpretation}\left(\mathit{oracles}\right),\; \forall output \in \operatorname{Fin}\left(2^{q}\right),\; \forall input \in \operatorname{Fin}\left(2^{q}\right),\; \operatorname{onBinaryLabels}\left(\operatorname{circuit}\left(\mathit{oracles}, q\right), \mathit{environment}, \mathit{output}, \mathit{input}\right) = \operatorname{invSqrtN}\left(q\right) \cdot \operatorname{omega}\left(q\right)^{\operatorname{val}\left(\mathit{output}\right) \cdot \operatorname{val}\left(\mathit{input}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Entries.circuit_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

invSqrtN q is the reciprocal square root of two to the q, and omega q is exp(2 pi i / 2^q). This assembly consumes the original no-swap width induction and the actual terminal reversal. circuit_action consumes this entry law to identify every vector with the existing analytic transform.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Entries.circuit_entry`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](Core/Base/Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](Primitives/QFT/Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](Primitives/QFT/Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](Primitives/QFT/Source/Matrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix](Primitives/QFT/Source/NoSwapMatrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix](Primitives/QFT/Source/Reverse/Matrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](Util/FinPow/BitReverse.md)
