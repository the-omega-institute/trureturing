# Primitives QFT Source NoSwapMatrix

## Abstract

Addressed quantum circuit: Primitives QFT Source NoSwapMatrix

**Lemma 1.1 (hadamard entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.hadamard_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.hadamard_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma hadamard_entry (output input : Fin 2) : Gate.HOp output input = invSqrt2 * (if output = 1 ∧ input = 1 then -1 else 1).

**Lemma 1.2 (qftSource noSwap binaryMatrix entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.qftSource_noSwap_binaryMatrix_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.qftSource_noSwap_binaryMatrix_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Closed matrix formula for the actual recursive no-swap circuit. Its row label is bit-reversed because the final symmetric SWAP network has not yet been applied.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.hadamard_entry`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/NoSwapMatrix.qftSource_noSwap_binaryMatrix_entry`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Operator](../../../Components/Gates/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](../Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](Matrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence](Recurrence.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/Complex](../../../Util/Complex.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](../../../Util/FinPow/BitReverse.md)
