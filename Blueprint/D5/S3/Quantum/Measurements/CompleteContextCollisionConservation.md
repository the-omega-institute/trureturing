# Complete Context Collision Conservation

## Abstract

Complete complementary rank-one measurements conserve collisions at operator and scalar level.

**Theorem 1.1 (Complete context collision conservation).**

$$\forall n: Nat, C: \operatorname{Fin}(n + 2) \to \operatorname{RankOneContext}(n + 1),\ \rho: \operatorname{Matrix}(\operatorname{Fin}(n + 1), \operatorname{Fin}(n + 1), \mathbb{C}),\\{}(\forall l: \operatorname{Fin}(n + 2), \operatorname{IsRecordMeasurement}(\operatorname{projector}(C_{l}))) \land\\{}(\forall l, k: \operatorname{Fin}(n + 2), j, r: \operatorname{Fin}(n + 1),\\{}\operatorname{Tr}(\operatorname{projector}(C_{l}, j) \cdot \operatorname{projector}(C_{k}, r)) = \operatorname{if}(l = k, \operatorname{if}(j = r, 1, 0), \frac{1}{n + 1})) \land\\{}\operatorname{PosSemidefinite}(\rho) \land \operatorname{Tr}(\rho) = 1 \Rightarrow\\{}(\sum_{l} \sum_{j} \operatorname{Kronecker}(\operatorname{projector}(C_{l}, j), \operatorname{projector}(C_{l}, j)) = I_{\operatorname{Matrix}((\operatorname{Fin}(n + 1) \times \operatorname{Fin}(n + 1)), (\operatorname{Fin}(n + 1) \times \operatorname{Fin}(n + 1)), \mathbb{C})} + \operatorname{PermMatrix}(\operatorname{prodComm}(\operatorname{Fin}(n + 1), \operatorname{Fin}(n + 1)))) \land\\{}(\sum_{l} \sum_{j} \operatorname{basisProbability}(\rho, C_{l}, j)^{2} = 1 + \operatorname{ReTr}(\rho^{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CompleteContextCollisionConservation.complete_context_collision_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take n+2 complete rank-one record measurements in dimension n+1. Their public trace-overlap equation states orthogonality within each context and inverse-dimension overlap between contexts.

The frozen complete-context tomography theorem separates matrices by their projector traces. Applying that separator to the induced frame map and then evaluating on matrix units gives the operator identity with the canonical coordinate-swap permutation matrix.

The scalar collision clause is the frozen complete-context purity identity applied to the same context family and density matrix. Prime-dimensional Weyl context families are instances of these public complete-context hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CompleteContextCollisionConservation.complete_context_collision_conservation`
- Dependency: [D5/S3/Quantum/Measurements/CompleteContextPurityIdentities](CompleteContextPurityIdentities.md)
