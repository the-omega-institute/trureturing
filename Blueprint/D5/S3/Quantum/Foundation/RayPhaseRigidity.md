# Connected ray tests and global phase

## Abstract

A support-connected family of invariant rays determines a unitary global phase.

Let iota be a finite decidable index type, possibly empty, let A be a complex matrix on iota, and let S be a set of complex vectors on iota. Ray preservation means that A x lies in the complex span of x. Support connectivity means that every pair of indices is linked by the reflexive-transitive closure of the relation that holds when some x in S is nonzero at both indices. If A is unitary, preserves the ray of single i 1 for every i, preserves the ray of every x in S, and S is support-connected, then there is c in C with norm(c) = 1 and A = c times the identity matrix. Sparse test supports are allowed; in the empty case c = 1. The statement makes no claim about CP maps, density supports, or computational semantics.

**Definition 1.1 (Invariance of a complex line).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] \forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \forall x \in iota\to\mathbb{C},\; \operatorname{PreservesRay}\left(A, x\right) \Leftrightarrow \operatorname{mulVec}\left(A, x\right)\in \operatorname{span}\left(\mathbb{C}, \{x\}\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RayPhaseRigidity.PreservesRay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of x lies in its complex span. At zero the condition is automatic. For a unitary and nonzero x the inclusion gives equality of rays.

**Definition 1.2 (Connectivity through test supports).**

$$\forall iota \in Type,\; \forall S \in \operatorname{Set}\left(iota\to\mathbb{C}\right),\; \operatorname{RaySupportConnected}\left(S\right) \Leftrightarrow \left(\forall i \in iota,\; \forall j \in iota,\; \operatorname{ReflTransGen}\left((p,q)\mapsto \exists x \in iota\to\mathbb{C},\; x\in S \land \left(x(p)\neq 0 \land x(q)\neq 0\right), i, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RayPhaseRigidity.RaySupportConnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two coordinates are adjacent when a test vector is nonzero at both. ReflTransGen is the reflexive transitive closure of this relation. Every pair of coordinates must be linked by a finite chain. Tests may have sparse supports; neither a full-support test nor a positive dimension is required.

**Theorem 1.3 (Connected invariant ray tests force a global phase).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; A\in \operatorname{unitaryGroup}\left(iota, \mathbb{C}\right) \Rightarrow \left(\left(\forall i \in iota,\; \operatorname{PreservesRay}\left(A, \operatorname{single}\left(i, 1\right)\right)\right) \Rightarrow \left(\forall S \in \operatorname{Set}\left(iota\to\mathbb{C}\right),\; \left(\forall x \in iota\to\mathbb{C},\; x\in S \Rightarrow \operatorname{PreservesRay}\left(A, x\right)\right) \Rightarrow \left(\operatorname{RaySupportConnected}\left(S\right) \Rightarrow \left(\exists c \in \mathbb{C},\; \Vert c\Vert = 1 \land A = c\cdot\operatorname{IdentityMatrix}\left(iota\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RayPhaseRigidity.unitary_phase_of_connected_ray_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate-ray invariance removes all off-diagonal entries. A test vector gives a common diagonal coefficient on every nonzero coordinate in its support. Induction along support chains propagates this equality to every pair of coordinates. Hence A = c I; unitarity gives conjugate(c) c = 1 and norm(c) = 1. In dimension zero choose c = 1. For one coordinate, reflexivity supplies connectivity even with no tests.

Application to Proposition 7.6: equal subspace images under U and V imply that W = V adjoint times U preserves every ray. The coordinate rays and the all-ones ray satisfy the theorem's premises: the singleton family containing the all-ones vector connects every pair of coordinates in one step. Thus W = c I and U = c V, with norm(c) = 1. This uses at most cardinality(iota) + 1 ray tests. The statement concerns linear images of subspaces; density-support and CP-map semantics are outside its scope.

Reuse boundary: Mathlib's LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent supplies scalarity from all-vector collinearity. The repository's sparse_probe_coercivity bounds the scalar defect using one normalized full-support probe. The present theorem supplies propagation across a connected family even when every test has sparse support. No literature originality is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.PreservesRay`
- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.RaySupportConnected`
- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.unitary_phase_of_connected_ray_tests`
