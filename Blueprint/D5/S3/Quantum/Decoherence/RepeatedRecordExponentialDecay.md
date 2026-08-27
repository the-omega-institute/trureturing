# Repeated Record Exponential Decay

## Abstract

Repeated finite records contract cross-class coherence at the uniform Gram rate.

**Theorem 1.1 (Repeated records converge exponentially to record-class pinching).**

$$\forall d: Nat, e: Nat,\\{}E: \operatorname{Fin}\left(d\right) \to \left(\operatorname{Fin}\left(e\right) \to \mathbb{C}\right),\\{}\forall i \in \operatorname{Fin}\left(d\right),\; \sum_{a \in \operatorname{Fin}\left(e\right)} \left\lVert E\left(i\right)\left(a\right) \right\rVert \cdot \left\lVert E\left(i\right)\left(a\right) \right\rVert = 1,\\{}q: \operatorname{Ico}\left(0, 1\right),\\{}{\forall i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; E\left(i\right) \ne E\left(j\right) \Rightarrow \left\lVert \operatorname{recordGram}\left(E, i, j\right) \right\rVert \le q} \Rightarrow\\{}\operatorname{let} Pch: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \rho\mapsto \sum_{l \in \operatorname{range}\left(E\right)} \operatorname{recordClassProjector}\left(E, l\right) \cdot \rho \cdot \operatorname{recordClassProjector}\left(E, l\right); \left(\forall N \in Nat, rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; \operatorname{entry}\left(\operatorname{iterate}\left(\operatorname{recordChannel}\left(E\right), N, \rho\right), i, j\right) = \operatorname{recordGram}\left(E, i, j\right)^{N} \cdot \operatorname{entry}\left(\rho, i, j\right)\right) \land \left(\left(\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; \operatorname{entry}\left(Pch\left(\rho\right), i, j\right) = \operatorname{ite}\left(E\left(i\right) = E\left(j\right), \operatorname{entry}\left(\rho, i, j\right), 0\right)\right) \land \left(\forall N \in Nat, rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \left\lVert \operatorname{iterate}\left(\operatorname{recordChannel}\left(E\right), N, \rho\right) - Pch\left(\rho\right) \right\rVert \le q^{N} \cdot \left\lVert \rho - Pch\left(\rho\right) \right\rVert\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay.repeated_record_exponential_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The record amplitudes construct both the Gram channel and the class projectors. The projector sum therefore uses the actual equality classes of environment records.

The first clause is the exact entrywise iterate. The second computes the projector sum, and the final clause is its Frobenius norm contraction under the stated cross-class Gram bound.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay.repeated_record_exponential_decay`
- Dependency: [D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel](EnvironmentMarginalChannel.md)
