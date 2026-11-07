# Connected ray tests and global phase

## Abstract

A support-connected family of invariant rays determines a unitary global phase.

Source: AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14, Proposition 7.6, atom 3702db2486a73bbef7dfe05f2d409f45820b15e5114b6a8119c255462339f23a. The scope is finite complex coordinate spaces, including the empty index type. The theorem needs only the coordinate rays and a family of test rays whose supports connect the coordinates. No individual test vector must have full support. A scalar of norm one expresses the source's global phase. The commentary about CP branches and computational semantics is outside this theorem.

**Definition 1.1 (Invariance of a complex line).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] \forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \forall x \in iota\to\mathbb{C},\; \operatorname{PreservesRay}\left(A, x\right) \Leftrightarrow \operatorname{mulVec}\left(A, x\right)\in \operatorname{span}\left(\mathbb{C}, \{x\}\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RayPhaseRigidity.PreservesRay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of x lies in its complex span. At zero the condition is automatic. For a unitary and nonzero x the inclusion gives equality of rays.

**Definition 1.2 (Invariance of every complex ray).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] \forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; \operatorname{RayPreserving}\left(A\right) \Leftrightarrow \left(\forall x \in iota\to\mathbb{C},\; \operatorname{PreservesRay}\left(A, x\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RayPhaseRigidity.RayPreserving` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the property of the relative unitary V adjoint times U in Proposition 7.6.

**Definition 1.3 (Connectivity through test supports).**

$$\forall iota \in Type,\; \forall S \in \operatorname{Set}\left(iota\to\mathbb{C}\right),\; \operatorname{RaySupportConnected}\left(S\right) \Leftrightarrow \left(\forall i \in iota,\; \forall j \in iota,\; \operatorname{ReflTransGen}\left((p,q)\mapsto \exists x \in iota\to\mathbb{C},\; x\in S \land \left(x(p)\neq 0 \land x(q)\neq 0\right), i, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/RayPhaseRigidity.RaySupportConnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two coordinates are adjacent when a test vector is nonzero at both. ReflTransGen is the reflexive transitive closure of this relation. Every pair of coordinates must be linked by a finite chain. Tests may have sparse supports; neither a full-support test nor a positive dimension is required.

**Theorem 1.4 (Connected invariant ray tests force a global phase).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall A \in \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; A\in \operatorname{unitaryGroup}\left(iota, \mathbb{C}\right) \Rightarrow \left(\left(\forall i \in iota,\; \operatorname{PreservesRay}\left(A, \operatorname{single}\left(i, 1\right)\right)\right) \Rightarrow \left(\forall S \in \operatorname{Set}\left(iota\to\mathbb{C}\right),\; \left(\forall x \in iota\to\mathbb{C},\; x\in S \Rightarrow \operatorname{PreservesRay}\left(A, x\right)\right) \Rightarrow \left(\operatorname{RaySupportConnected}\left(S\right) \Rightarrow \left(\exists c \in \mathbb{C},\; \Vert c\Vert = 1 \land A = c\cdot\operatorname{IdentityMatrix}\left(iota\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RayPhaseRigidity.unitary_phase_of_connected_ray_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate-ray invariance removes all off-diagonal entries. A test vector gives a common diagonal coefficient on every nonzero coordinate in its support. Induction along support chains propagates this equality to every pair of coordinates. Hence A = c I; unitarity gives conjugate(c) c = 1 and norm(c) = 1. In dimension zero choose c = 1. For one coordinate, reflexivity supplies connectivity even with no tests.

Application to Proposition 7.6: equal subspace images under U and V imply that W = V adjoint times U preserves every ray. The coordinate rays and the all-ones ray satisfy the theorem's premises: the singleton family containing the all-ones vector connects every pair of coordinates in one step. Thus W = c I and U = c V, with norm(c) = 1. This uses at most cardinality(iota) + 1 ray tests. The statement concerns linear images of subspaces; density-support and CP-map semantics are outside its scope.

Reuse boundary: Mathlib's LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent supplies scalarity from all-vector collinearity. The repository's sparse_probe_coercivity bounds the scalar defect using one normalized full-support probe. The present theorem supplies propagation across a connected family even when every test has sparse support. No literature originality is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.PreservesRay`
- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.RayPreserving`
- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.RaySupportConnected`
- Truth anchor: `D5/S3/Quantum/Foundation/RayPhaseRigidity.unitary_phase_of_connected_ray_tests`
