# Connection Coefficient Multiplication

## Abstract

Typed completion paths retain coefficient order, factor roles, and certificate status.

**Theorem 1.1 (Connection coefficients multiply along typed completion paths).**

$$\left(\forall V \in Type, R \in Type, X \in V, Y \in V, Z \in V, edgeWeight \in \operatorname{EdgeWeight}\left(V, R\right), firstStep \in \operatorname{Hom}\left(X, Y\right), secondStep \in \operatorname{Hom}\left(Y, Z\right),\; \left(\operatorname{Quiver}\left(V\right) \land \operatorname{Monoid}\left(R\right)\right) \Rightarrow \operatorname{pathWeight}\left(edgeWeight, \operatorname{completedPath}\left(firstStep, secondStep\right)\right) = edgeWeight\left(firstStep\right) \cdot edgeWeight\left(secondStep\right)\right) \land \left(\left(\forall V \in Type, R \in Type, X \in V, Y \in V, Z \in V, edgeWeight \in \operatorname{EdgeWeight}\left(V, R\right), firstStep \in \operatorname{Hom}\left(X, Y\right), secondStep \in \operatorname{Hom}\left(Y, Z\right),\; \left(\operatorname{Quiver}\left(V\right) \land \operatorname{Monoid}\left(R\right)\right) \Rightarrow \operatorname{FactorsAlongCompletedPath}\left(edgeWeight, edgeWeight\left(firstStep\right) \cdot edgeWeight\left(secondStep\right), \operatorname{completedPath}\left(firstStep, secondStep\right), firstStep, secondStep\right)\right) \land \left(\left(\forall V \in Type, X \in V, Y \in V, Z \in V, firstStep \in \operatorname{Hom}\left(X, Y\right), secondStep \in \operatorname{Hom}\left(Y, Z\right),\; \operatorname{Quiver}\left(V\right) \Rightarrow \left(\neg \operatorname{IsPrimitiveConnectionPath}\left(\operatorname{completedPath}\left(firstStep, secondStep\right)\right)\right)\right) \land \left(\left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{ramanujanRadical}\left(x\right) = gaussianMassFactor \cdot \operatorname{exponentialFlowFactor}\left(x\right) \cdot \operatorname{scaleJacobianFactor}\left(x\right)\right) \land \left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{IsStructuralConstantCompositionCertificate}\left(x, ramanujanCompletionPath\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first three conjuncts quantify typed Quiver edges X to Y and Y to Z. Path weight multiplication is the pinned Mathlib theorem Quiver.Path.weight_comp; the same path is explicitly identified as the completed factorization and has length two, so it is not a one-edge primitive.

The fourth conjunct is the positive-real Ramanujan 541 identity in the named Gaussian-total-mass, exponential-flow, and scale-Jacobian factors.

The fifth conjunct gives the factorization structural-composition certificate status. Its predicate checks the exact three-edge Ramanujan path, the ordered role list, non-primitiveness, and agreement of the radical with the path weight. Permuting the roles therefore changes the certified statement even though real multiplication is commutative.

## References

- Truth anchor: `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication`
