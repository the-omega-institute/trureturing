# Components Gates Swap Coordinates

## Abstract

Addressed quantum circuit: Components Gates Swap Coordinates

**Lemma 1.1 (encoded bit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.encoded_bit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.encoded_bit` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma encoded_bit {width : Nat} (basis : Fin width → Fin 2) (index : Fin width) : (QuantumSignature.qubitsIndexEquiv width basis).val.testBit (WireAddress.bitIndex index).val = finTwoEquiv (basis index).

**Lemma 1.2 (decoded bit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.decoded_bit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.decoded_bit` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma decoded_bit {width : Nat} (label : Fin (2 ^ width)) (index : Fin width) : finTwoEquiv ((QuantumSignature.qubitsIndexEquiv width).symm label index) = label.val.testBit (WireAddress.bitIndex index).val.

**Lemma 1.3 (qftSwapLabel coordinates).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapLabel_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapLabel_coordinates` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The unchanged integer-label action exchanges exactly the two physical coordinates.

**Lemma 1.4 (qftSwapOperator coordinates entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapOperator_coordinates_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapOperator_coordinates_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Every matrix entry of the original target is the same exact coordinate exchange.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.decoded_bit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.encoded_bit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapLabel_coordinates`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates.qftSwapOperator_coordinates_entry`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label](Label.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Operator](Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator](../../QubitPrimitive/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator](../../../Core/Base/Control/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation](../../../Core/Base/Gate/Unitary/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](../../../Util/FinPow/BinaryBasis.md)
