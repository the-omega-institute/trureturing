# Events of the original QFT circuit

## Abstract

Events of the original QFT circuit

**Theorem 1.1 (Every event coordinate of the same circuit).**

$$\forall oracles \in \mathit{OracleModel},\; \forall event \in \operatorname{Event}\left(\operatorname{quantum}\left(\operatorname{FourierModel}\left(\right), \mathit{oracles}\right)\right),\; \forall q \in \mathit{Nat},\; \operatorname{count}\left(\mathit{event}, \operatorname{eventCost}\left(\operatorname{circuit}\left(\mathit{oracles}, q\right)\right)\right) = q \cdot \operatorname{delta}\left(\operatorname{hadamard}\left(\right), \mathit{event}\right) + \operatorname{choose}\left(q, 2\right) \cdot \operatorname{delta}\left(\operatorname{controlledPhase}\left(\right), \mathit{event}\right) + \operatorname{natDiv}\left(q, 2\right) \cdot \operatorname{delta}\left(\operatorname{swap}\left(\right), \mathit{event}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.qftSource_circuit_event_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

delta(a,event) is one if the gate event a equals event and zero otherwise. natDiv is natural-number division. eventCost traverses the same construction tree used by matrix execution. The counts are q Hadamards, choose(q,2) native controlled phases and floor(q/2) native SWAPs; every other coordinate, including oracle events, has count zero. The empty-width circuit has all counts zero. These are ideal native occurrences, not default-model expansions or hardware costs.

The phase-prefix induction counts one controlled phase at each actual step. The no-swap induction adds one Hadamard and the selected prefix. The reversal word retains its certified disjoint parallel branches and contains exactly floor(q/2) SWAP occurrences. Their sequential composition is precisely Source.circuit, also used by circuit_action.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.qftSource_circuit_event_count`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool](../../../Core/Base/Accounting/ResourcePool.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement](../../../Core/Base/UnitaryCircuit/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive](Primitive.md)
