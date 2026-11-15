# Components Gates Swap Physical

## Abstract

Addressed quantum circuit: Components Gates Swap Physical

**Definition 1.1 (positions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.positions`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.positions` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private def positions : Fin 2 ↪ Fin count.

**Lemma 1.2 (dimensions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.dimensions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.dimensions` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma dimensions (index : Fin 2) : (layout.wire index).dimension = (ambient.wire (positions left right distinct index)).dimension.

**Definition 1.3 (placedOperator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.placedOperator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.placedOperator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Place the independent exact SWAP target on the two requested physical wires.

**Definition 1.4 (circuitAt).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.circuitAt`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.circuitAt` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Run the entire native expansion at the requested left and right positions.

**Lemma 1.5 (swap circuitAt matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.swap_circuitAt_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.swap_circuitAt_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The physically placed implementation retains the exact SWAP on every input.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.circuitAt`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.dimensions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.placedOperator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.positions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical.swap_circuitAt_matrix`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap](../Swap.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement](../../../Core/Base/UnitaryCircuit/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries](../../../Core/Base/UnitaryCircuit/Placement/Entries.md)
