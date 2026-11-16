# Primitives QFT Source Recurrence

## Abstract

Addressed quantum circuit: Primitives QFT Source Recurrence

**Lemma 1.1 (phase binaryMatrix pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phase_binaryMatrix_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phase_binaryMatrix_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma phase_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (phaseLayer oracles n) environment (qftPairEquiv n (outputHead, outputTail)) (qftPairEquiv n (inputHead, inputTail)) = if outputHead = inputHead ∧ outputTail = inputTail then (if inputHead = 1 then ω (n + 1) ^ inputTail.val else 1) else 0.

**Lemma 1.2 (phaseAfterLeading binaryMatrix pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phaseAfterLeading_binaryMatrix_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phaseAfterLeading_binaryMatrix_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma phaseAfterLeading_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : ((onBinaryLabels (phaseLayer oracles n) environment : HilbertOperator (Qubits (n + 1))) * (onBinaryLabels (leadingHadamard oracles n) environment : HilbertOperator (Qubits (n + 1)))) (qftPairEquiv n (outputHead, outputTail)) (qftPairEquiv n (inputHead, inputTail)) = (if outputHead = 1 then ω (n + 1) ^ outputTail.val else 1) * Gate.HOp outputHead inputHead * (if outputTail = inputTail then 1 else 0).

**Lemma 1.3 (qftSource noSwap succ binaryMatrix pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.qftSource_noSwap_succ_binaryMatrix_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.qftSource_noSwap_succ_binaryMatrix_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSource_noSwap_succ_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (noSwap oracles (n + 1)) environment (qftPairEquiv n (outputHead, outputTail)) (qftPairEquiv n (inputHead, inputTail)) = onBinaryLabels (noSwap oracles n) environment outputTail inputTail * (if outputHead = 1 then ω (n + 1) ^ inputTail.val else 1) * Gate.HOp outputHead inputHead.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phaseAfterLeading_binaryMatrix_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.phase_binaryMatrix_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Recurrence.qftSource_noSwap_succ_binaryMatrix_pair`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Operator](../../../Components/Gates/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](../Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries](BinaryEntries.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](Matrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix](PhaseMatrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](../../../Util/FinPow/BitReverse.md)
