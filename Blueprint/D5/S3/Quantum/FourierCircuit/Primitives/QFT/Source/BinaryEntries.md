# Primitives QFT Source BinaryEntries

## Abstract

Addressed quantum circuit: Primitives QFT Source BinaryEntries

**Lemma 1.1 (binary pair decode).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.binary_pair_decode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.binary_pair_decode` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma binary_pair_decode (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) : (QuantumSignature.qubitsIndexEquiv (n + 1)).symm (qftPairEquiv n (head, tail)) = Fin.cons head ((QuantumSignature.qubitsIndexEquiv n).symm tail).

**Lemma 1.2 (qftSource binaryMatrix pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_binaryMatrix_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_binaryMatrix_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSource_binaryMatrix_pair {oracles : OracleModel} {n : Nat} (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout (n + 1))) (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels body environment (qftPairEquiv n (rowHead, rowTail)) (qftPairEquiv n (columnHead, columnTail)) = (body.matrix environment) (Fin.cons rowHead ((QuantumSignature.qubitsIndexEquiv n).symm rowTail)) (Fin.cons columnHead ((QuantumSignature.qubitsIndexEquiv n).symm columnTail)).

**Lemma 1.3 (qftSource leading binaryMatrix pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_leading_binaryMatrix_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_leading_binaryMatrix_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSource_leading_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (leadingHadamard oracles n) environment (qftPairEquiv n (rowHead, rowTail)) (qftPairEquiv n (columnHead, columnTail)) = if rowTail = columnTail then Gate.HOp rowHead columnHead else 0.

**Lemma 1.4 (qftSource tail binaryMatrix pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_tail_binaryMatrix_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_tail_binaryMatrix_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSource_tail_binaryMatrix_pair (oracles : OracleModel) (n : Nat) (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n)) (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) (environment : oracles.Interpretation) : onBinaryLabels (tailLayer oracles n body) environment (qftPairEquiv n (rowHead, rowTail)) (qftPairEquiv n (columnHead, columnTail)) = if rowHead = columnHead then onBinaryLabels body environment rowTail columnTail else 0.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.binary_pair_decode`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_binaryMatrix_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_leading_binaryMatrix_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/BinaryEntries.qftSource_tail_binaryMatrix_pair`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries](LeadingEntries.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](Matrix.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries](TailEntries.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](../../../Util/FinPow/BinaryBasis.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair](../../../Util/FinPow/BinaryBasis/Pair.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](../../../Util/FinPow/BitReverse.md)
