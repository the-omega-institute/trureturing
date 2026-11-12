# Base Norm Contraction

## Abstract

Positive normalization-preserving dynamics contract the cone base norm.

**Theorem 1.1 (Strict positivity implies nonnegativity on the whole cone).**

$$\forall V, C, u, x,\\{}\operatorname{AddCommGroup}\left(V\right) \land \operatorname{Module}\left(\operatorname{Real}\left(\right), V\right) \land \operatorname{ConvexCone}\left(C, V\right) \land \operatorname{RealLinearFunctional}\left(u, V\right) \land \operatorname{StrictlyPositive}\left(u, C\right) \land x \in C \Rightarrow 0 \leq \operatorname{Eval}\left(u, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/BaseNormContraction.functional_nonneg_on_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any additive commutative group V with a real module structure, any real convex cone C and any real-linear functional u strictly positive on every nonzero element of C, u is nonnegative at every element of C, including zero. No norm, dimension, closedness or generating hypothesis is used. In cone_decomposition_costs_bddBelow, this nonnegativity bounds every cone-decomposition cost below by zero. In OriginalMassCalibration.original_mass_factorization, applying the same result to CD and CE gives nonnegative values for both actual mass tensors.

**Theorem 1.2 (Positive normalized dynamics are base-norm contractions).**

$$\forall V, C, u, T, t, x,\\{}\operatorname{ConvexCone}\left(C, V\right) \land \operatorname{Generates}\left(C, V\right) \land \operatorname{StrictlyPositive}\left(u, C\right) \land\\{}(\forall s, T_{s}(C) \subseteq C \land u \circ T_{s} = u) \Rightarrow \\{}\operatorname{baseNorm}\left(C, u, T_{t}(x)\right) \leq \operatorname{baseNorm}\left(C, u, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/BaseNormContraction.positive_normalization_preserving_dynamics_contracts_base_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a real vector space and C a convex cone that generates V by differences. A real-linear functional u is strictly positive on every nonzero cone element.

The base norm is constructed as the infimum of u(a)+u(b) over all cone decompositions x=a-b. Thus the norm object is built from the source cone and functional rather than assumed as an unrelated ambient norm.

For every time, the real-linear dynamics maps C into C and preserves u. Applying it to any decomposition of x produces a cone decomposition of the evolved vector with exactly the same cost.

The decomposition-cost set for x is therefore contained in the one for its image. Reversed monotonicity of infima gives the stated contraction.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/BaseNormContraction.functional_nonneg_on_cone`
- Truth anchor: `D5/S3/Quantum/Dynamics/BaseNormContraction.positive_normalization_preserving_dynamics_contracts_base_norm`
