# Connection Coefficient Multiplication

## Abstract

Typed completion paths retain coefficient order, factor roles, and certificate status.

**Theorem 1.1 (Connection coefficients multiply along typed completion paths).**

$$\left(\forall a \in \mathbb{R}, b \in \mathbb{R}, X \in \mathbb{R}, Y \in \mathbb{R}, Z \in \mathbb{R},\; \operatorname{IsCoefficientBearingCompletionChain}\left(a, b, X, Y, Z\right) \Rightarrow \left(Z = (a \cdot b) \cdot X \land \left(\operatorname{pathWeight}\left(\operatorname{completionChainStepWeight}\left(a, b\right), completionChainPath\right) = a \cdot b \land \left(\neg \operatorname{IsPrimitiveConnectionPath}\left(completionChainPath\right)\right)\right)\right)\right) \land \left(\left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{ramanujanRadical}\left(x\right) = gaussianMassFactor \cdot \operatorname{exponentialFlowFactor}\left(x\right) \cdot \operatorname{scaleJacobianFactor}\left(x\right)\right) \land \left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{ramanujanRadical}\left(x\right) = \operatorname{pathWeight}\left(\operatorname{ramanujanStepWeight}\left(x\right), ramanujanCompletionPath\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first branch binds a, b, X, Y, and Z once. The named IsCoefficientBearingCompletionChain bridge says that X, Y, Z are the state values on the typed source-middle-target path and that a and b are the weights of its first and second edges.

Under that one bridge, the first three semantic conjuncts are the boxed scalar conclusion Z equals (ab)X, the explicit equality between the completed-path weight and ab, and non-primitiveness of that same two-edge path. The weight equality applies the pinned Mathlib theorem Quiver.Path.weight_comp.

The fourth semantic conjunct is the positive-real Ramanujan 541 identity in the named Gaussian-total-mass, exponential-flow, and scale-Jacobian factors.

The fifth semantic conjunct is the structural-composition certificate: on the same positive-real domain, the radical equals the weight of the named typed Ramanujan completion path. No custom conclusion predicate contains additional propositions.

## References

- Truth anchor: `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication`
