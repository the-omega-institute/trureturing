# Block Causal Quotient Decomposition

## Abstract

Block-product intervention channels decompose causal equivalence and its quotient.

**Theorem 1.1 (Causal equivalence and the causal quotient decompose by blocks).**

$$\left(\forall M \in \operatorname{BlockModel}\left(I\right), N \in \operatorname{BlockModel}\left(I\right),\; \left(\forall a \in \operatorname{JointIntervention}\left(I\right),\; \operatorname{blockInterventionalOutcome}\left(a, M\right) = \operatorname{blockInterventionalOutcome}\left(a, N\right)\right) \Leftrightarrow \left(\forall i \in I,\; \forall u \in \operatorname{Action}\left(i\right),\; \operatorname{apply}\left(M, i, u\right) = \operatorname{apply}\left(N, i, u\right)\right)\right) \land \left(\forall M \in \operatorname{BlockModel}\left(I\right),\; \operatorname{causalQuotientEquiv}\left(\operatorname{globalClass}\left(M\right)\right) = \operatorname{localClasses}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/BlockCausalQuotientDecomposition.causal_equivalence_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the block index be finite. Each block has a nonempty allowed intervention type and a local response channel. A joint intervention is the unrestricted product of those local interventions, and its response is assembled coordinatewise.

Two block models agree under every joint intervention exactly when their local channels agree under every intervention in every block. The reverse direction inserts a chosen local action into a baseline joint intervention.

The global and local causal quotients use the existing empirical setoid. The named canonical equivalence is Mathlib's indexed quotient-product equivalence after transporting along the first clause, and it sends each global class to its family of local classes.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/BlockCausalQuotientDecomposition.causal_equivalence_block_decomposition`
- Dependency: [D5/S3/ConceptDynamics/EmpiricalIdentifiability](../EmpiricalIdentifiability.md)
