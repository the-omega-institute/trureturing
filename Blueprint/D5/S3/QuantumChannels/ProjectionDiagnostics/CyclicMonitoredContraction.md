# Cyclic monitored observability

## Abstract

The actual cyclic monitored restriction has no nonzero all-future hidden vector.

**Theorem 1.1 (The actual cyclic restriction has zero future kernel).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)],\quad\forall U \in \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, E, E\right),\; \forall v \in E,\; \forall x \in \operatorname{cyclicSpace}\left(U, v\right),\; \left(\forall n \in \mathbb{N},\; \operatorname{cyclicClick}\left(U, v, (\operatorname{cyclicStep}\left(U, v\right)^n) x\right)=0\right) \Rightarrow x=0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction.cyclic_future_kernel_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional complex Hilbert space, every unitary U, and every vector v, C is the span of the actual forward orbit U^n v. The operator T_C is the restriction of (I-P_v)U and B_C is the restriction of P_v U. Both preserve C. The theorem includes v=0 and requires no recurrence premise. Orthogonal observability duality identifies the ambient hidden space; maximal unobservability gives its invariance under the monitored step. On its intersection with C the monitored step equals U. Finite dimensional injectivity supplies surjectivity of this restricted U, hence inverse invariance. Every hidden cyclic vector is then orthogonal to every U^n v and must vanish. This observability conclusion supplies the zero dark space needed for cyclic power contraction. A strict power norm bound and the infinite weighted return identity are not asserted here. The recurrence and expected-return result is classical: Grunbaum, Velazquez, Werner and Werner, arXiv:1202.3903v3, Theorem 2.

## References

- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction.cyclic_future_kernel_eq_bot`
- Dependency: [D5/S3/ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality](../../ObserverMemory/Dynamics/InfiniteObservabilityOrthogonalDuality.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](../../ObserverMemory/Dynamics/MaximalUnobservableSubspace.md)
- Dependency: [D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredReturnConservation](MonitoredReturnConservation.md)
