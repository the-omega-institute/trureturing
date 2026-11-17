# Original recursive QFT circuit

## Abstract

Original recursive QFT circuit

**Theorem 1.1 (Exact action on every vector).**

$$\forall oracles \in \mathit{OracleModel},\; \forall q \in \mathit{Nat},\; \forall environment \in \operatorname{Interpretation}\left(\mathit{oracles}\right),\; \forall v \in \operatorname{ComplexVector}\left(2^{q}\right),\; \operatorname{mulVec}\left(\operatorname{onBinaryLabels}\left(\operatorname{circuit}\left(\mathit{oracles}, q\right), \mathit{environment}\right), v\right) = \operatorname{QFT}\left(2^{q}, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Correctness.circuit_action` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

ComplexVector m denotes Fin m to Complex. The interpreter is computed from the actual circuit construction. It executes the leading Hadamard, the ordered controlled-phase prefix, the recursively placed tail and the terminal disjoint parallel SWAP network. The theorem holds for every natural width q, including zero, every oracle interpretation and every complex input vector. The right side is the existing independently defined QuantumPhaseEstimationGeneral.QFT, with positive exponent and inverse square-root normalization. Equality preserves the full phase, including global phase.

Binary labels are big endian. Before the terminal swaps the output label in the proved matrix formula is bit reversed. The actual parallel reversal cancels that reversal. The proof retains the original phase-prefix induction, the no-swap width induction and the reversal action on every computational basis ket. It does not assign Fourier semantics as an input to the circuit.

For Chapter 15 at q equal to three, an input x with bits x2,x1,x0 has output tensor factors in frequency MSB-to-LSB order with phases 2 pi times 0.x0, 0.x1x0 and 0.x2x1x0, each divided by the square root of two. For x equal to five these phases are pi, pi/2 and 5 pi/4. This describes the convention of the universal action theorem; the fixed example does not replace it.

The matching event theorem observes the identical circuit value. Its ideal native counts do not claim data-loading, full classical readout, discrete gate synthesis or hardware cost.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Correctness.circuit_action`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](Core/Base/Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Entries](Entries.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](Primitives/QFT/Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](Primitives/QFT/Source/Matrix.md)
- Dependency: [D5/S3/Quantum/ShorCountingMarginal](../ShorCountingMarginal.md)
