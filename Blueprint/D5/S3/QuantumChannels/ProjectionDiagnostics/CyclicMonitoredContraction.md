# Cyclic monitored observability

## Abstract

The actual cyclic monitored restriction has no nonzero all-future hidden vector.

**Theorem 1.1 (The actual cyclic restriction has zero future kernel).**

$$\forall x \in C, (\forall n \in \mathbb{N}, B_C T_C^n x=0)\implies x=0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction.cyclic_future_kernel_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional complex Hilbert space, every unitary U, and every vector v, C is the span of the actual forward orbit U^n v. The operator T_C is the restriction of (I-P_v)U and B_C is the restriction of P_v U. Both preserve C. The theorem includes v=0 and requires no recurrence premise. Orthogonal observability duality identifies the ambient hidden space; maximal unobservability gives its invariance under the monitored step. On its intersection with C the monitored step equals U. Finite dimensional injectivity supplies surjectivity of this restricted U, hence inverse invariance. Every hidden cyclic vector is then orthogonal to every U^n v and must vanish. This is the structural no-dark obligation for the registered cyclic contraction route. A strict power norm bound and the infinite weighted return identity are not asserted here. The recurrence and expected-return result is classical: Grunbaum, Velazquez, Werner and Werner, arXiv:1202.3903v3, Theorem 2.

## References

- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction.cyclic_future_kernel_eq_bot`
- Dependency: [D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality](../../ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](../../ObserverMemory/Dynamics/MaximalUnobservableSubspace.md)
- Dependency: [D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredReturnConservation](MonitoredReturnConservation.md)
