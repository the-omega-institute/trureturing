# Residual Join Law

## Abstract

Joining one definition filters the target residual by that definition's kernel.

**Theorem 1.1 (A joined definition intersects the target residual).**

$$\forall X, C, D, Y: Type,\\{}q: \operatorname{Concept}\left(X, C\right), d: \operatorname{Concept}\left(X, D\right), T: \operatorname{Concept}\left(X, Y\right),\\{}\operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, d\right), T\right) = \operatorname{intersection}\left(\operatorname{defectRelation}\left(q, T\right), \operatorname{ker}\left(d\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw.residual_join_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary state, baseline-coordinate, definition-coordinate, and target types, q, d, and T are concept readouts on the same state space. The source notation E is represented by the canonical defectRelation, q join d by conceptJoin, and ker d by the Setoid kernel of d on state pairs.

The accepted concept-kernel order duality confirms the component kernel identity when both coordinate types share a universe. The public law retains independent coordinate universes: product projections extract the two component equalities, and reassociation of the target-inequality clause gives exactly the displayed residual intersection.

The Lean module also checks a nonempty Boolean instance: constant baseline and definition readouts leave false and true in the joined residual for the identity target. This witnesses the domains and shows the equality is not certified only on an empty residual.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw.residual_join_law`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
