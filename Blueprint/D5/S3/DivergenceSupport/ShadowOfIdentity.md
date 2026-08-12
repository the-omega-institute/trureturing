# Shadows of Identities

## Abstract

A named nonnegative remainder turns an exact identity into its shadow inequality, with Cauchy-Schwarz as the kinematic instance.

An inequality is the shadow of an identity when its slack is not merely known to be nonnegative: the slack is identified with a named explicit remainder supplied by the identity. IsShadow records both parts. This distinction is the point of the definition; dropping the name would retain only an ordinary inequality.

The definition earns its place in the kinematic instance. The frozen Lagrange-Gram identity supplies the exact Cauchy-Schwarz slack, and its explicit double sum is proved locally nonnegative as a nested sum of squares. Cauchy-Schwarz is then obtained solely by applying is_shadow_le; it is not reproved by an independent inequality argument.

The proposed statistical instance was dropped honestly. The suggested identity 0 = 0 - (-KL) simplifies to 0 = KL and is false in general. Writing IsShadow 0 KL KL would only repackage Gibbs nonnegativity together with the tautology KL - 0 = KL, with no separate identity producing the slack. Only the kinematic family is instantiated here.

The source note also asserts that the statistical and kinematic families descend respectively from normalization and positivity, and that both reduce to one source. That structural claim is not formalized in this module. No physical or information-theoretic interpretation is claimed.

**Definition 1.1 (A shadow names an explicit nonnegative remainder).**

$$\operatorname{IsShadow}(lhs, rhs, remainder) : \operatorname{Prop} = (rhs - lhs) = remainder \land 0\le remainder$$

*Formalization.* `D5/S3/DivergenceSupport/ShadowOfIdentity.IsShadow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsShadow lhs rhs remainder asserts the exact slack equation rhs - lhs = remainder and the nonnegativity 0 <= remainder. The named quantity is therefore part of the content, not an after-the-fact label for an already known inequality.

**Theorem 1.2 (A shadow implies its inequality).**

$$\forall lhs, rhs, remainder \operatorname{IsShadow}(lhs, rhs, remainder) \Rightarrow lhs \le rhs$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ShadowOfIdentity.is_shadow_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Once the explicit remainder is nonnegative, the identity rhs - lhs = remainder gives lhs <= rhs. This extraction discards only the named remainder; it does not replace the identity with an unmotivated inequality.

**Theorem 1.3 (The Lagrange-Gram slack is an explicit shadow remainder).**

$$\operatorname{IsShadow} ((\sum_{i} u_{i} v_{i})^{2}), ((\sum_{i} u_{i}^{2}) \times (\sum_{i} v_{i}^{2})), \frac{1}{2} \sum_{i} \sum_{j} (u_{i} v_{j} - u_{j} v_{i})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ShadowOfIdentity.lagrange_gram_is_shadow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set s and real families u and v, the squared dot product is a shadow of the product of the squared-norm sums. The named remainder is one half of the double sum over i and j of (u i v j - u j v i)^2. The identity is imported from the frozen Lagrange-Gram module, while nonnegativity is proved here by summing squares and dividing by the positive constant two.

**Theorem 1.4 (Cauchy-Schwarz follows by extracting the shadow inequality).**

$$(\sum_{i} u_{i} v_{i})^{2} \le (\sum_{i} u_{i}^{2}) \times (\sum_{i} v_{i}^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/ShadowOfIdentity.cauchy_schwarz_of_lagrange_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cauchy-Schwarz is derived solely by applying is_shadow_le to the frozen Lagrange-Gram shadow. The theorem therefore demonstrates why the definition carries mathematical weight: the explicit remainder and its local positivity are the bridge from the identity to the inequality.

## References

- Truth anchor: `D5/S3/DivergenceSupport/ShadowOfIdentity.IsShadow`
- Truth anchor: `D5/S3/DivergenceSupport/ShadowOfIdentity.cauchy_schwarz_of_lagrange_gram`
- Truth anchor: `D5/S3/DivergenceSupport/ShadowOfIdentity.is_shadow_le`
- Truth anchor: `D5/S3/DivergenceSupport/ShadowOfIdentity.lagrange_gram_is_shadow`
- Dependency: [D5/S3/QuantumBounds/LagrangeGramIdentity](../QuantumBounds/LagrangeGramIdentity.md)
