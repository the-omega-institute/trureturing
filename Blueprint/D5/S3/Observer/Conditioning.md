# Finite Record Conditioning

## Abstract

Finite projective record measurements preserve trace and define idempotent unread conditioning.

**Theorem 1.1 (Record weights sum to the original trace).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\operatorname{Record}(P) \Rightarrow \sum_{k\in\kappa}w_{k}(\rho)=\operatorname{tr}(\rho),\quad w_{k}(\rho):=\operatorname{tr}(\rho P_{k}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning.recordWeight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n and kappa be finite index types, let rho be an arbitrary complex n-by-n matrix, and let P be a complete pairwise orthogonal family of self-adjoint idempotents. The record weight w_k(rho) is the Born weight trace(rho P_k). Linearity of trace and the completeness identity sum_k P_k = 1 give the displayed normalization. No positivity, Hermiticity, or trace-one premise is imposed on rho.

**Theorem 1.2 (Discarding the record preserves trace).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\operatorname{Record}(P) \Rightarrow \operatorname{tr}(U_{P}(\rho))=\operatorname{tr}(\rho),\\U_{P}(\rho):=\sum_{k\in\kappa}P_{k} \rho P_{k}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning.unreadState_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unread matrix U_P(rho) is the finite sum of the diagonal record compressions P_k rho P_k. Cyclicity of trace and P_k squared equal to P_k reduce each compressed trace to w_k(rho); the record-weight sum then recovers trace(rho). This is an algebraic trace-preservation statement for arbitrary rho, not a claim that the file develops a general completely positive channel theory.

**Theorem 1.3 (Forgetting the record is idempotent).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\operatorname{Record}(P) \Rightarrow U_{P}(U_{P}(\rho))=U_{P}(\rho).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning.unreadState_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairwise orthogonality removes every cross-record block when U_P is applied a second time, while projection idempotence leaves each diagonal block unchanged. Consequently repeated unread measurement equals one unread measurement. The result again requires no state positivity or normalization assumption.

**Theorem 1.4 (Unread fixed points have no off-diagonal record blocks).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\operatorname{Record}(P) \Rightarrow U_{P}(\rho)=\rho \Leftrightarrow \forall k,l\in\kappa,\ k\neq l \Rightarrow P_{k} \rho P_{l}=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning.unreadState_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A matrix is fixed by U_P exactly when every block P_k rho P_l with distinct record labels vanishes. In the forward direction, compressing the fixed-point identity isolates an off-diagonal block and orthogonality kills it. Conversely, completeness expands rho into record columns; removing the off-diagonal columns leaves precisely the sum defining U_P(rho). The equivalence concerns arbitrary complex matrices, not only density matrices.

**Theorem 1.5 (Nonzero conditional branches are states).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\forall k\in\kappa,\ \operatorname{Record}(P) \land \operatorname{PosSemidef}(\rho) \land \operatorname{tr}(\rho)=1 \land w_{k}(\rho)\neq 0 \Rightarrow\\\operatorname{PosSemidef}(\rho_{k}) \land \operatorname{tr}(\rho_{k})=1,\\\rho_{k}:=w_{k}(\rho)^{-1}\cdot P_{k} \rho P_{k}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning.conditionalState_isState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume rho is positive semidefinite with trace one and the selected record weight is nonzero. Self-adjointness of P_k makes the compression P_k rho P_k positive semidefinite, while the Born-weight theorem makes w_k(rho) nonnegative. Scaling by its inverse therefore preserves positivity, and the compressed trace cancels the nonzero weight to give trace one. The definition uses a totalized inverse, but this theorem explicitly excludes a zero-weight outcome.

**Theorem 1.6 (The unread matrix is the weighted conditional ensemble).**

$$\forall n,\kappa\ [\operatorname{Fintype}(n)]\ [\operatorname{Fintype}(\kappa)],\\\forall P: \kappa\to M_{n}(\mathbb{C}),\ \rho\in M_{n}(\mathbb{C}),\\\operatorname{Record}(P) \land \operatorname{PosSemidef}(\rho) \Rightarrow\\U_{P}(\rho)=\sum_{k\in\kappa}w_{k}(\rho)\cdot \rho_{k},\\\rho_{k}:=w_{k}(\rho)^{-1}\cdot P_{k} \rho P_{k}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning.unread_eq_weighted_ensemble` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite rho, a zero record weight forces the corresponding positive compressed block P_k rho P_k to have zero trace and hence vanish. For every nonzero weight, multiplication by w_k(rho) cancels the inverse in rho_k. Thus every term agrees with its unread compression and summing gives U_P(rho), without excluding zero-weight outcomes or requiring trace-one normalization.

## References

- Truth anchor: `D5/S3/Observer/Conditioning.conditionalState_isState`
- Truth anchor: `D5/S3/Observer/Conditioning.recordWeight_sum`
- Truth anchor: `D5/S3/Observer/Conditioning.unreadState_fixed_iff`
- Truth anchor: `D5/S3/Observer/Conditioning.unreadState_idempotent`
- Truth anchor: `D5/S3/Observer/Conditioning.unreadState_trace`
- Truth anchor: `D5/S3/Observer/Conditioning.unread_eq_weighted_ensemble`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../Quantum/FiniteDimensional.md)
