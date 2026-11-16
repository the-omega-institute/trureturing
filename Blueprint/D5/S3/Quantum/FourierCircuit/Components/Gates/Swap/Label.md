# Components Gates Swap Label

## Abstract

Addressed quantum circuit: Components Gates Swap Label

**Definition 1.1 (qftSwapLabel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Basis-label action of the usual three-CNOT addressed SWAP.

**Lemma 1.2 (qftSwapLabel left).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_left` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSwapLabel_left {n : Nat} (left right : Fin n) (hne : left ≠ right) (label : Fin (2 ^ n)) : (qftSwapLabel left right label).val.testBit (WireAddress.bitIndex left).val = label.val.testBit (WireAddress.bitIndex right).val.

**Lemma 1.3 (qftSwapLabel right).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_right` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSwapLabel_right {n : Nat} (left right : Fin n) (hne : left ≠ right) (label : Fin (2 ^ n)) : (qftSwapLabel left right label).val.testBit (WireAddress.bitIndex right).val = label.val.testBit (WireAddress.bitIndex left).val.

**Lemma 1.4 (qftSwapLabel of ne).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_of_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_of_ne` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSwapLabel_of_ne {n : Nat} (left right bit : Fin n) (hne : left ≠ right) (hleft : bit ≠ left) (hright : bit ≠ right) (label : Fin (2 ^ n)) : (qftSwapLabel left right label).val.testBit (WireAddress.bitIndex bit).val = label.val.testBit (WireAddress.bitIndex bit).val.

**Lemma 1.5 (qftSwapOperator applyVec ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapOperator_applyVec_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapOperator_applyVec_ket` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma qftSwapOperator_applyVec_ket {n : Nat} (left right : Fin n) (hne : left ≠ right) (label : Fin (2 ^ n)) : (qftSwapOperator left right hne).applyVec (NormalizedVector.ket (R.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_left`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_of_ne`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapLabel_right`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label.qftSwapOperator_applyVec_ket`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Operator](Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator](../../QubitPrimitive/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../../../Core/Base/Gate/Unitary.md)
