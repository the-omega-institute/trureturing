# Environment Marginal Channel

## Abstract

A finite controlled environment record reduces to its Gram entrywise channel.

**Theorem 1.1 (Finite environment marginal is the record Gram channel).**

$$\forall d \in Nat, e \in Nat, E \in \operatorname{Fin}\left(d\right) \to \left(\operatorname{Fin}\left(e\right) \to \mathbb{C}\right), rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{let} V: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall i: \operatorname{Fin}\left(d\right), a: \operatorname{Fin}\left(e\right), j: \operatorname{Fin}\left(d\right), \operatorname{entry}\left(V, \operatorname{pair}\left(i, a\right), j\right) = \operatorname{ite}\left(j = i, E\left(i\right)\left(a\right), 0\right); \operatorname{let} T: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right), \mathbb{C}\right), i: \operatorname{Fin}\left(d\right), j: \operatorname{Fin}\left(d\right), \operatorname{entry}\left(T\left(X\right), i, j\right) = \sum_{a \in \operatorname{Fin}\left(e\right)} \operatorname{entry}\left(X, \operatorname{pair}\left(i, a\right), \operatorname{pair}\left(j, a\right)\right); \left(T\left(V \cdot \rho \cdot V^{*}\right) = \operatorname{recordChannel}\left(E, \rho\right) \land T\left(V \cdot \rho \cdot V^{*}\right) = \operatorname{hadamard}\left((i, j) \mapsto \operatorname{recordGram}\left(E, i, j\right), \rho\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right), j \in \operatorname{Fin}\left(d\right),\; \operatorname{entry}\left(T\left(V \cdot \rho \cdot V^{*}\right), i, j\right) = \operatorname{recordGram}\left(E, i, j\right) \cdot \operatorname{entry}\left(\rho, i, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel.environment_marginal_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite system and environment coordinate sets, the displayed matrix V writes the environment amplitudes belonging to each system address. The displayed environment trace sums equal environment coordinates.

For every complex system matrix, tracing V rho V^* gives the canonical recordChannel and also the Hadamard product of rho with the canonical recordGram matrix. The final clause states the same calculation at each system-matrix entry.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel.environment_marginal_channel`
- Dependency: [D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality](../FixedAlgebra/SingletonRecordClassicality.md)
