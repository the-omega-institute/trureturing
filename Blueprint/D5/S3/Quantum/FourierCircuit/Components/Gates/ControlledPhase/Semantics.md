# Components Gates ControlledPhase Semantics

## Abstract

Addressed quantum circuit: Components Gates ControlledPhase Semantics

**Definition 1.1 (phaseWeight).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phaseWeight`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phaseWeight` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private def phaseWeight (angle : Real) (bit : Fin 2) : Complex.

**Lemma 1.2 (cnot twice).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.cnot_twice`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.cnot_twice` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma cnot_twice (basis : layout.Basis) : AlgorithmGate.cnotPermutation (AlgorithmGate.cnotPermutation basis) = basis.

**Lemma 1.3 (conjugate diagonal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.conjugate_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.conjugate_diagonal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma conjugate_diagonal (register : Register) (permutation : Equiv.Perm register.Index) (involution : Function.Involutive permutation) (weight : register.Index → Complex) : ((UnitaryOperator.ofPerm (R.

**Lemma 1.4 (target diagonal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.target_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.target_diagonal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma target_diagonal (angle : Real) : (operator angle : HilbertOperator layout.register) = Matrix.diagonal (fun basis => qftControlledPhaseFactor (n.

**Lemma 1.5 (phase product).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phase_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phase_product` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma phase_product (angle : Real) (basis : layout.Basis) : phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation basis) (1 : Fin 2)) * (phaseWeight (angle / 2) (basis (1 : Fin 2)) * phaseWeight (angle / 2) (basis (0 : Fin 2))) = qftControlledPhaseFactor (n.

**Lemma 1.6 (word diagonal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.word_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.word_diagonal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma word_diagonal (oracles : OracleModel) (angle : Real) (environment : oracles.Interpretation) : (((circuit oracles angle).matrix environment) : HilbertOperator layout.register) = Matrix.diagonal (fun basis => phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation basis) (1 : Fin 2)) * (phaseWeight (angle / 2) (basis (1 : Fin 2)) * phaseWeight (angle / 2) (basis (0 : Fin 2)))).

**Lemma 1.7 (controlledPhase circuit matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.controlledPhase_circuit_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.controlledPhase_circuit_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The complete five-gate native word realizes the original target with exact phase.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.cnot_twice`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.conjugate_diagonal`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.controlledPhase_circuit_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phaseWeight`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phase_product`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.target_diagonal`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.word_diagonal`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation](../../GateModel/Algorithm/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Construction](Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Operator](Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement](Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Canonical](../../../Core/Base/Gate/Placement/Canonical.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/Complex](../../../Util/Complex.md)
