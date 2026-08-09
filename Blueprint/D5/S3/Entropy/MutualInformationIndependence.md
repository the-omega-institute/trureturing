# Vanishing Mutual Information Characterizes Independence

## Abstract

Finite classical mutual information in nats vanishes exactly when the joint mass function is the product of its own marginals.

**Theorem 1.1 (Zero mutual information characterizes independence).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\\operatorname{mutualInformation}(p)=0 \Leftrightarrow \\p=((i,j)\mapsto \operatorname{marginal}(p)(i)\operatorname{marginal}((j,i)\mapsto p(i,j))(j)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformationIndependence.mutual_information_eq_zero_iff_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem states that mutual information vanishes exactly when the joint mass function equals the product of its own two marginals, which is the finite independence characterization. Its only hypotheses are nonnegativity and normalization of the joint; no strict positivity is assumed, and zero-mass cells are permitted. The units are nats because mutualInformation uses the Real.log divergence. This module defines nothing.

This theorem closes the cluster: wave 16 supplied nonnegativity, wave 17b supplied vanishing on product laws, and the converse here makes the independence characterization an if and only if. The proof applies the frozen GibbsEquality.kl_divergence_eq_zero_iff theorem to the product-of-marginals reference. Its three reference-law premises are discharged here, not assumed: that product is shown nonnegative and normalized, and the required absolute-continuity premise is proved by showing that a zero reference cell forces the corresponding joint cell to be zero. These are the same three discharges already performed by the nonnegativity result.

An audit of this program found that the nonnegativity theorem constrains the reference not at all, since the bound holds for any admissible reference, and that vanishing on products constrains it only on the product submanifold. This converse constrains the reference wherever mutual information vanishes.

That is a stronger attestation, but it is not a full attestation of the definition. A corrupted reference that agrees with the true reference on every joint where the divergence vanishes would still escape this characterization.

Nothing is claimed about the rate at which mutual information grows away from independence. No conditional independence statement is proved, and nothing beyond two coordinates is asserted.

## References

- Truth anchor: `D5/S3/Entropy/MutualInformationIndependence.mutual_information_eq_zero_iff_product`
- Dependency: [D5/S3/Divergence/GibbsEquality](../Divergence/GibbsEquality.md)
- Dependency: [D5/S3/Entropy/MutualInformation](MutualInformation.md)
