# Nonnegativity of Finite Classical Mutual Information

## Abstract

Finite classical mutual information in nats is nonnegative for every nonnegative normalized joint mass function.

**Theorem 1.1 (Finite classical mutual information is nonnegative).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\0\le \operatorname{mutualInformation}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformation.mutual_information_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mutual information is the divergence of the joint distribution from the product of its own two marginals. The marginal definition from D5/S3/Divergence/ChainRule is deliberately reused for both coordinates: the first directly, and the second by evaluating that same marginal on the swapped joint fun r => p (r.2, r.1), so no second marginal is defined. This reuse is deliberate: marginal remains the single source of truth.

The bound is D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg applied to the product reference; all three of its premises are discharged here, not assumed. The product of marginals is nonnegative because each marginal is a finite sum of nonnegative joint masses. The product reference is normalized: each marginal sum collapses to the joint sum, and the product of the two unit sums is one. It is absolutely continuous because each joint mass is bounded by each of its marginals, so a vanishing product forces a vanishing joint mass. Nothing about nonnegativity of divergence is re-proved.

The nonnegativity bound holds for any admissible reference and therefore does not by itself certify that the reference is the product of the joint's own marginals. The mutual-information content resides entirely in the definition, which is where a reader should look. Concretely, the reference at (i, j) is the first marginal at i times the second marginal at j, and the second marginal is obtained by evaluating the same marginal function on the coordinate-swapped joint fun r => p (r.2, r.1); a reader must not misread this as a second copy of the first marginal.

The hypotheses are nonnegativity and normalization of the joint only, not strict positivity. Zero-mass cells are permitted. The units are nats, consistent with klDivergence and with the bucket's entropy definition.

This module proves nonnegativity only; it does not characterize the equality case that I = 0 exactly when the joint equals the product of its marginals, equivalently independence. It does not relate mutual information to Shannon entropy: no I = H(X) + H(Y) - H(X,Y) identity is established here. It says nothing about conditional mutual information or about more than two coordinates.

## References

- Truth anchor: `D5/S3/Entropy/MutualInformation.mutual_information_nonneg`
- Dependency: [D5/S3/Divergence/ChainRule](../Divergence/ChainRule.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../Divergence/GrandmotherTheorem.md)
