# Mutual Information Vanishes on Product Laws

## Abstract

Finite classical mutual information in nats vanishes on every normalized product mass function.

**Theorem 1.1 (Mutual information vanishes on product laws).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall a: \iota\to \mathbb{R}, b: \kappa\to \mathbb{R},\\((\forall i, 0\le a(i)) \land \sum_{i}a(i)=1) \land\\((\forall j, 0\le b(j)) \land \sum_{j}b(j)=1) \Rightarrow\\\operatorname{mutualInformation}((i,j)\mapsto a(i)b(j))=0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformationProduct.mutual_information_product_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem states that mutual information vanishes on a product joint, the independent case. The factors a and b need only be nonnegative and normalized; no strict positivity is assumed. Zero-mass cells are permitted, and their terms vanish. The units are nats, consistent with the bucket's other entropy modules. This module defines nothing; it uses the imported mutualInformation and marginal definitions.

This identity is a definition pin, not merely another consequence of divergence nonnegativity. The nonnegativity theorem holds for any reference that is nonnegative, normalized, and absolutely continuous, so it does not certify that mutualInformation uses the product of the joint's own marginals. By forcing the imported definition to reduce to zero on normalized product joints, this theorem constrains the reference itself, in particular the coordinate swap used to obtain the second marginal. The proof names the swapped second marginal explicitly as hswapped_second_marginal rather than collapsing the mutualInformation definition immediately, so the swap-specific content is present in the proof.

A corrupted reference that reuses the first marginal for both coordinates can typecheck when the index types coincide. On the positive Bool example a = (3/4, 1/4) and b = (1/4, 3/4), that reference remains nonnegative, normalized, and absolutely continuous, so it survives the nonnegativity theorem, but it gives one half of log 3 instead of zero. The product identity rejects that corruption.

The residual limitation is plain: this identity tests the reference only on product joints. It is blind to any reference that agrees with the product of the marginals on independent joints but differs on correlated ones. Correlated joints are exactly where mutual information does its work. This confirms the reduction to independence at the boundary; it does not verify the reference on correlated joints. Accordingly, the mutualInformation definition is not fully attested by this theorem.

This is one direction only. It does not prove the converse that vanishing mutual information forces the joint to be a product, equivalently independence. That converse would require the equality case of the divergence bound, and it is not established here.

## References

- Truth anchor: `D5/S3/Entropy/MutualInformationProduct.mutual_information_product_eq_zero`
- Dependency: [D5/S3/Entropy/MutualInformation](MutualInformation.md)
