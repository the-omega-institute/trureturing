# Connection Coefficient Multiplication

## Abstract

Typed completion paths retain coefficient order, factor roles, and certificate status.

**Theorem 1.1 (Connection coefficients multiply along typed completion paths).**

$$\left(\forall a \in \mathbb{R}, b \in \mathbb{R}, X \in \mathbb{R}, Y \in \mathbb{R}, Z \in \mathbb{R},\; \operatorname{IsCoefficientBearingCompletionChain}\left(a, b, X, Y, Z\right) \Rightarrow \left(Z = (a \cdot b) \cdot X \land \left(\operatorname{FactorsAlongCompletedPath}\left(\operatorname{completionChainStepWeight}\left(a, b\right), a \cdot b, firstCompletionStep, secondCompletionStep\right) \land \left(\neg \operatorname{IsPrimitiveConnectionPath}\left(completionChainPath\right)\right)\right)\right)\right) \land \left(\left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{ramanujanRadical}\left(x\right) = gaussianMassFactor \cdot \operatorname{exponentialFlowFactor}\left(x\right) \cdot \operatorname{scaleJacobianFactor}\left(x\right)\right) \land \left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{IsStructuralConstantCompositionCertificate}\left(x, ramanujanCompletionPath\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first branch binds a, b, X, Y, and Z once. The named IsCoefficientBearingCompletionChain bridge says that X, Y, Z are the state values on the typed source-middle-target path and that a and b are the weights of its first and second edges.

Under that one bridge, the first three semantic conjuncts are the boxed scalar conclusion Z equals (ab)X, one completed-path factorization, and non-primitiveness of that same two-edge path. The factorization applies the pinned Mathlib theorem Quiver.Path.weight_comp; there is no duplicate raw weight clause.

The fourth semantic conjunct is the positive-real Ramanujan 541 identity in the named Gaussian-total-mass, exponential-flow, and scale-Jacobian factors.

The fifth semantic conjunct gives the structural-composition certificate status. The predicate itself includes x positive, the exact three-edge Ramanujan path, the ordered role list, non-primitiveness, and agreement of the radical with the path weight. Thus x equals zero is not a certificate, and permuting the roles changes the certified statement.

## References

- Truth anchor: `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication`
