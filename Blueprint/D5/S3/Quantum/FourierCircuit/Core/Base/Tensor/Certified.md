# Core Base Tensor Certified

## Abstract

Addressed quantum circuit: Core Base Tensor Certified

**Definition 1.1 (Certified tensor operator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For arbitrary finite registers R and S and unitary operators U and V, UnitaryOperator.prodTensor U V is their Kronecker product reindexed by Register.prodIndexEquiv R S. Its unitary certificate uses the two input unitary certificates.

**Lemma 1.2 (Tensor entry helper).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor_apply` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every finite R and S, U : UnitaryOperator R, V : UnitaryOperator S and i,j : (Register.prod R S).Index, prodTensor U V i j = U i.1 j.1 * V i.2 j.2. The public entry lemma below consumes this helper.

**Lemma 1.3 (unitaryOperator prodTensor apply).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.unitaryOperator_prodTensor_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.unitaryOperator_prodTensor_apply` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Every product-register entry is the product of the two actual subsystem entries.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor_apply`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.unitaryOperator_prodTensor_apply`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../Gate/Unitary.md)
