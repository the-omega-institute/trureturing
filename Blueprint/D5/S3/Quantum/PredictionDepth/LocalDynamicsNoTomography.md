# Local Dynamics Do Not Complete Tomography

## Abstract

A Heisenberg dynamics preserving the two local sectors cannot generate a nonzero cross-factor correlation direction.

**Theorem 1.1 (Local-sector closure excludes nonzero correlation readouts).**

$$\forall m: \operatorname{Nat}, n: \operatorname{Nat}, \operatorname{NeZero}(m), \operatorname{NeZero}(n), H: \operatorname{LinearMap}(\mathbb{R}, \operatorname{BipartiteHermitian}(m, n), \operatorname{BipartiteHermitian}(m, n)), (\forall x: \operatorname{BipartiteHermitian}(m, n), x \in \operatorname{Sup}(\operatorname{localASector}(m, n), \operatorname{localBSector}(m, n)) \Rightarrow H(x) \in \operatorname{Sup}(\operatorname{localASector}(m, n), \operatorname{localBSector}(m, n))) \Rightarrow (\forall t: \operatorname{Nat}, x: \operatorname{BipartiteHermitian}(m, n), x \in \operatorname{Sup}(\operatorname{localASector}(m, n), \operatorname{localBSector}(m, n)) \Rightarrow H^{t} x \in \operatorname{Sup}(\operatorname{localASector}(m, n), \operatorname{localBSector}(m, n)) \land \forall t: \operatorname{Nat}, x: \operatorname{BipartiteHermitian}(m, n), x \in \operatorname{Sup}(\operatorname{localASector}(m, n), \operatorname{localBSector}(m, n)) \Rightarrow H^{t} x \in \operatorname{correlationSector}(m, n) \Rightarrow H^{t} x = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography.local_dynamics_no_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite bipartite Hermitian carrier is split into the canonical A-local, B-local, and correlation sectors.

For any Heisenberg linear dynamics that preserves the join of the two local sectors, every finite iterate remains local. Orthogonality of the correlation sector then forces any iterate lying in it to be zero.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography.local_dynamics_no_tomography`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
