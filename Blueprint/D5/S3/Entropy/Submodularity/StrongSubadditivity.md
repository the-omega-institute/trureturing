# Strong Subadditivity and Conditional Products

## Abstract

Finite Shannon entropy is submodular for three variables, with equality exactly when the last two variables factor conditionally on every active first-coordinate slice.

**Definition 1.1 (The XY projection sums out the third coordinate).**

$$p_{XY}(x, y)= \sum_{z} p(x, (y, z)).$$

*Formalization.* `D5/S3/Entropy/Submodularity/StrongSubadditivity.xyProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a mass function on the right-nested product X times (Y times Z), the XY projection sums over Z while retaining X and Y. The nesting is part of the interface because conditioning the original law on X must produce a joint law on Y times Z.

**Definition 1.2 (The XZ projection sums out the second coordinate).**

$$p_{XZ}(x, z)= \sum_{y} p(x, (y, z)).$$

*Formalization.* `D5/S3/Entropy/Submodularity/StrongSubadditivity.xzProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The XZ projection instead sums over Y. Both projections have the same first-coordinate marginal as the original law; their conditional laws are respectively the Y and Z marginals of the original conditional joint law.

**Theorem 1.3 (Conditional entropy is subadditive on each slice).**

$$\operatorname{conditionalEntropy}(p)\leq \operatorname{conditionalEntropy}(p_{XY})+ \operatorname{conditionalEntropy}(p_{XZ}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/StrongSubadditivity.conditionalEntropy_pair_le_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized nonnegative law, each slice with nonzero X marginal is a normalized joint law on Y times Z. Two-variable entropy subadditivity applies to that slice, and multiplication by its nonnegative X weight preserves the inequality.

A zero-marginal slice contributes zero to all three conditional entropies. Summing the slicewise inequalities therefore gives the conditional form without imposing a positivity hypothesis on every first-coordinate marginal.

**Theorem 1.4 (Entropy is submodular for three variables).**

$$H(p)+ H(p_{X})\leq H(p_{XY})+ H(p_{XZ}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/StrongSubadditivity.entropy_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the entropy chain rule to the original law and to both two-coordinate projections converts conditional subadditivity into the classical strong-subadditivity inequality. The common marginal terms cancel algebraically.

The statement uses the submodular arrangement H(X,Y,Z) plus H(X) at the left and H(X,Y) plus H(X,Z) at the right. All entropies are finite Shannon entropies in nats.

**Theorem 1.5 (Equality means conditional product factorization).**

$$\begin{gathered}H(p)+ H(p_{X})= H(p_{XY})+ H(p_{XZ}) \Leftrightarrow\\\forall x, p_{X}(x)\neq 0 \Rightarrow p(y, z\mid x)= p_{Y}(y\mid x) p_{Z}(z\mid x).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/StrongSubadditivity.entropy_submodular_eq_iff_conditional_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference between the two sides of conditional subadditivity is the sum over X of the slice weight times the mutual information of the conditional YZ law. Every summand is nonnegative on an active slice, so equality forces each such mutual information to vanish.

Vanishing finite mutual information is equivalent to the conditional joint law being the product of its Y and Z marginals. Conversely, that factorization makes every active summand vanish. Zero-marginal slices are deliberately excluded because their conditional law is the artificial zero-over-zero law and contributes no entropy.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/StrongSubadditivity.conditionalEntropy_pair_le_add`
- Truth anchor: `D5/S3/Entropy/Submodularity/StrongSubadditivity.entropy_submodular`
- Truth anchor: `D5/S3/Entropy/Submodularity/StrongSubadditivity.entropy_submodular_eq_iff_conditional_product`
- Truth anchor: `D5/S3/Entropy/Submodularity/StrongSubadditivity.xyProjection`
- Truth anchor: `D5/S3/Entropy/Submodularity/StrongSubadditivity.xzProjection`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](../ConditionalEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformationEntropy](../MutualInformationEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformationIndependence](../MutualInformationIndependence.md)
