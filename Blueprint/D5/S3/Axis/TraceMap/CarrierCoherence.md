# Carrier Coherence

## Abstract

The two named partial sums agree after a substitution and a depth shift.

Two formalizations of the same partial sum exist in this repository, written eight days apart. An earlier module related one of them to a sum at a shifted weight index, which is not either of the two objects the digestion ledger names. Its comment claimed more than its type did, and that module is frozen, so the correction is carried here.

The missing step turns out not to be combinatorial. Shifting the weight index by one is exactly substituting each reading by its own embedding, because the weight is an exponential in the corresponding power. With that substitution the earlier relation transports onto the two carriers themselves.

**Lemma 1.1 (Shifting the weight is scaling the readings).**

$$\operatorname{t}\left(x, y, k + 1\right) = \operatorname{t}\left(x \cdot \mathit{phi}, y \cdot \mathit{psi}, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/CarrierCoherence.axisWeight_succ_eq_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One step up in the weight index multiplies each reading by its own embedding, which is what turns an index shift into a parameter substitution.

**Lemma 1.2 (The two formalizations of the weight agree).**

$$\operatorname{tA}\left(x, y, k\right) = \operatorname{tB}\left(x, y, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/CarrierCoherence.axisWeight_agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same function written twice, eight days apart, under two names. Stating the agreement is what lets a theorem about one be used in a proof about the other.

**Theorem 1.3 (The two named partial sums agree).**

$$\operatorname{tracePartial}\left(x \cdot \mathit{phi}, y \cdot \mathit{psi}, K\right) = \operatorname{axisPartialSum}\left(x, y, K + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/CarrierCoherence.tracePartial_eq_axisPartialSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the two embeddings into the readings and shifting the depth by one carries one partial sum onto the other. Both shifts are explicit in the statement, and cutting either one makes the module fail to build.

## References

- Truth anchor: `D5/S3/Axis/TraceMap/CarrierCoherence.axisWeight_agree`
- Truth anchor: `D5/S3/Axis/TraceMap/CarrierCoherence.axisWeight_succ_eq_scaled`
- Truth anchor: `D5/S3/Axis/TraceMap/CarrierCoherence.tracePartial_eq_axisPartialSum`
- Dependency: [D5/S1/Recurrence/TraceMap](../../../S1/Recurrence/TraceMap.md)
- Dependency: [D5/S3/Axis/TraceMap/PartialSumBridge](PartialSumBridge.md)
