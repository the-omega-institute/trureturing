# Earliest Future Witness

## Abstract

Memory is the earliest future distinction of states merged by the current readout.

**Theorem 1.1 (Canonical memory records the first future mismatch).**

$$\forall Y, O: \operatorname{Type}, F: Y \to Y, q: Y \to O,\\{}x, y \in Y, n \in \mathbb{N},\\{}\operatorname{q}\left(x\right) = \operatorname{q}\left(y\right) \Rightarrow (\operatorname{shortestDistance}\left(F, q, x, y\right) = \operatorname{some}\left(n\right) \iff (0 < n \land \operatorname{I}\left(x, n\right) \neq \operatorname{I}\left(y, n\right) \land\\{}\forall m < n, \operatorname{I}\left(x, m\right) = \operatorname{I}\left(y, m\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/EarliestFutureWitness.memory_is_earliest_future_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume two states have the same current readout. Their canonical finite shortest distance is some positive depth exactly when their future readouts differ at that depth and agree at every earlier depth.

Thus the stored distinction is selected by the first future mismatch, rather than by an arbitrary record of the past. The theorem places no finiteness assumption on the state or readout carrier.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/EarliestFutureWitness.memory_is_earliest_future_witness`
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality](LocalCertificateMinimality.md)
