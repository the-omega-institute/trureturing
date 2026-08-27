# Complete Context Purity Identities

## Abstract

Complete complementary rank-one measurements express purity exactly in Born-probability coordinates.

**Theorem 1.1 (Complete context purity identities).**

$$\forall n: Nat, C: \operatorname{Fin}(n + 2) \to \operatorname{RankOneContext}(n + 1),\ \rho: \operatorname{Matrix}(\operatorname{Fin}(n + 1), \operatorname{Fin}(n + 1), \mathbb{C}),\\{}(\forall l: \operatorname{Fin}(n + 2), \operatorname{IsRecordMeasurement}(\operatorname{projector}(C_{l}))) \land\\{}(\forall l, k: \operatorname{Fin}(n + 2), j, r: \operatorname{Fin}(n + 1),\\{}\operatorname{Tr}(\operatorname{projector}(C_{l}, j) \cdot \operatorname{projector}(C_{k}, r)) = \operatorname{if}(l = k, \operatorname{if}(j = r, 1, 0), \frac{1}{n + 1})) \land\\{}\operatorname{PosSemidefinite}(\rho) \land \operatorname{Tr}(\rho) = 1 \Rightarrow\\{}(\sum_{l} \sum_{j} {\operatorname{basisProbability}(\rho, C_{l}, j) - \frac{1}{n + 1}}^{2} = \operatorname{ReTr}(\rho^{2}) - \frac{1}{n + 1}) \land\\{}(\sum_{l} \sum_{j} \operatorname{basisProbability}(\rho, C_{l}, j)^{2} = 1 + \operatorname{ReTr}(\rho^{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CompleteContextPurityIdentities.complete_context_purity_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take n+2 complete rank-one record measurements in dimension n+1. The public overlap equation gives Kronecker trace overlap within one context and constant inverse-dimension overlap between distinct contexts.

The overlap equation derives both pairwise orthogonality of the trace-zero measurement projections and reconstruction of every trace-zero Hermitian state. The existing probability Pythagoras theorem then has zero residual.

Each context's Born coordinates sum to one. Expanding the centered squares across all n+2 contexts therefore gives the equivalent uncentered identity: the total squared probability is one plus the real trace purity.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/CompleteContextPurityIdentities.complete_context_purity_identities`
- Dependency: [D5/S3/Quantum/Tomography/CompleteContextTomography](../Tomography/CompleteContextTomography.md)
- Dependency: [D5/S3/Quantum/Tomography/PurityPythagorasDecomposition](../Tomography/PurityPythagorasDecomposition.md)
