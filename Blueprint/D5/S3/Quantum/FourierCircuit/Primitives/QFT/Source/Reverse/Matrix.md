# Primitives QFT Source Reverse Matrix

## Abstract

Addressed quantum circuit: Primitives QFT Source Reverse Matrix

**Lemma 1.1 (swapStep binaryMatrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.swapStep_binaryMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.swapStep_binaryMatrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma swapStep_binaryMatrix (oracles : OracleModel) (n : Nat) (index : Fin (n / 2)) (environment : oracles.Interpretation) : onBinaryLabels (swapStep oracles n index) environment = qftSwapOperator (qftSwapLeft n index) (qftSwapRight n index) (qftSwapLeft_ne_right n index).

**Lemma 1.2 (reversePrefix binary apply ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.reversePrefix_binary_apply_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.reversePrefix_binary_apply_ket` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma reversePrefix_binary_apply_ket (oracles : OracleModel) (n count : Nat) (bounded : count ≤ n / 2) (label : Fin (2 ^ n)) (environment : oracles.Interpretation) : (onBinaryLabels (reversePrefix oracles n count bounded) environment).applyVec (NormalizedVector.ket (R.

**Lemma 1.3 (qftSource reverse binary apply ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binary_apply_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binary_apply_ket` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSource_reverse_binary_apply_ket (oracles : OracleModel) (n : Nat) (label : Fin (2 ^ n)) (environment : oracles.Interpretation) : (onBinaryLabels (bitReverse oracles n) environment).applyVec (NormalizedVector.ket (R.

**Lemma 1.4 (qftSource reverse binaryMatrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binaryMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binaryMatrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSource_reverse_binaryMatrix (oracles : OracleModel) (n : Nat) (environment : oracles.Interpretation) : onBinaryLabels (bitReverse oracles n) environment = UnitaryOperator.ofPerm (qftReverseBitsPerm n).

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binaryMatrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.qftSource_reverse_binary_apply_ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.reversePrefix_binary_apply_ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Matrix.swapStep_binaryMatrix`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label](../../../../Components/Gates/Swap/Label.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Operator](../../../../Components/Gates/Swap/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Kets](../../../../Components/Kets.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../../../../Core/Base/Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse](../../Mathematics/BitReverse.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](../Matrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](../../../../Util/FinPow/BitReverse.md)
