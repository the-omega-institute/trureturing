# Events of the original QFT circuit

## Abstract

Events of the original QFT circuit

**Lemma 1.1 (One actual controlled phase).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phaseStep_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phaseStep_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and offset : Fin n, count event (phaseStep oracles n offset).eventCost = delta(controlledPhase,event). The actual native leaf contributes one occurrence.

**Lemma 1.2 (Controlled-phase prefix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phasePrefix_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phasePrefix_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and count with bounded : count <= n, countEvent event (phasePrefix oracles n count bounded).eventCost = count * delta(controlledPhase,event). Here countEvent denotes ResourcePool.count. The proof follows the actual prefix recursion.

**Lemma 1.3 (One leading Hadamard).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.leadingHadamard_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.leadingHadamard_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles) and natural n, count event (leadingHadamard oracles n).eventCost = delta(hadamard,event).

**Lemma 1.4 (Placement preserves the tail count).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.tailLayer_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.tailLayer_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n), count event (tailLayer oracles n body).eventCost = count event body.eventCost. Physical placement preserves the original event trace.

**Lemma 1.5 (Recursive word before reversal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.noSwap_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.noSwap_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles) and natural n, count event (noSwap oracles n).eventCost = n * delta(hadamard,event) + choose(n,2) * delta(controlledPhase,event). The width induction consumes the leading, prefix and placed-tail counts.

**Lemma 1.6 (Actual reversal prefix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.reversePrefix_count`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.reversePrefix_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and count with bounded : count <= n/2, countEvent event (reversePrefix oracles n count bounded).eventCost = count * delta(swap,event), where countEvent is ResourcePool.count and division is natural-number division. This uses the event trace of the actual disjoint parallel reversal.

**Theorem 1.7 (Every event coordinate of the same circuit).**

$$\forall oracles \in \mathit{OracleModel},\; \forall event \in \operatorname{Event}\left(\operatorname{quantum}\left(\operatorname{FourierModel}\left(\right), \mathit{oracles}\right)\right),\; \forall q \in \mathit{Nat},\; \operatorname{count}\left(\mathit{event}, \operatorname{eventCost}\left(\operatorname{circuit}\left(\mathit{oracles}, q\right)\right)\right) = q \cdot \operatorname{delta}\left(\operatorname{hadamard}\left(\right), \mathit{event}\right) + \operatorname{choose}\left(q, 2\right) \cdot \operatorname{delta}\left(\operatorname{controlledPhase}\left(\right), \mathit{event}\right) + \operatorname{natDiv}\left(q, 2\right) \cdot \operatorname{delta}\left(\operatorname{swap}\left(\right), \mathit{event}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.qftSource_circuit_event_count` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

delta(a,event) is one if the gate event a equals event and zero otherwise. natDiv is natural-number division. eventCost traverses the same construction tree used by matrix execution. The counts are q Hadamards, choose(q,2) native controlled phases and floor(q/2) native SWAPs; every other coordinate, including oracle events, has count zero. The empty-width circuit has all counts zero. These are ideal native occurrences, not default-model expansions or hardware costs.

The phase-prefix induction counts one controlled phase at each actual step. The no-swap induction adds one Hadamard and the selected prefix. The reversal word retains its certified disjoint parallel branches and contains exactly floor(q/2) SWAP occurrences. Their sequential composition is precisely Source.circuit, also used by circuit_action.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.leadingHadamard_count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.noSwap_count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phasePrefix_count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phaseStep_count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.qftSource_circuit_event_count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.reversePrefix_count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.tailLayer_count`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool](../../../Core/Base/Accounting/ResourcePool.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement](../../../Core/Base/UnitaryCircuit/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive](Primitive.md)
