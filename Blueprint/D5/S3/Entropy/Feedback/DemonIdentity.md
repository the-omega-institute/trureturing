# The Feedback Divergence Identity

## Abstract

The average posterior-to-reference divergence of a finite joint law equals its mutual information plus the input-marginal divergence from the reference.

**Theorem 1.1 (Average posterior divergence is mutual information plus input divergence).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall P: \iota\times\kappa\to \mathbb{R}, u: \iota\to \mathbb{R},\\(\forall q, 0\le P q) \Rightarrow (\forall x, 0< u x) \Rightarrow\\\operatorname{klDivergence}(P, (x,y)\mapsto u(x)\cdot\operatorname{marginal}((j,i)\mapsto P(i,j))(y))=\\\operatorname{mutualInformation}(P)+\operatorname{klDivergence}(\operatorname{marginal}(P), u)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Feedback/DemonIdentity.demon_average_divergence_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonnegative joint mass function P over a product index set and a strictly positive reference u on the first coordinate, the average of the posterior-to-reference relative entropies weighted by the output marginal, assembled here in joint form as the relative entropy of P against the product of u with the output marginal, equals the mutual information of P plus the relative entropy of the input marginal from u. The mutual information, marginal, and relative entropy are the repository's own definitions, so the displayed identity relates existing objects without introducing new ones.

The proof works pointwise on the joint support. Where P is positive the input marginal, the output marginal, and the reference are all positive there, so the logarithm of the reference ratio splits into a mutual-information term and an input-divergence term; where P vanishes the weight annihilates the term. Summing over the second coordinate collapses the input-divergence contribution, because summing the joint law over that coordinate is exactly the input marginal.

This is not a restatement of a library lemma. Mathlib supplies the logarithm product and quotient laws and the finite double-sum reindexing; the repository supplies relative entropy, the marginal, and mutual information. The identity is the load-bearing decomposition behind the feedback reading, in which the average gain of an observer equals the mutual information at a reference-matched input. It does not claim the thermodynamic accounting or the reference-matched corollary, only the divergence decomposition itself.

## References

- Truth anchor: `D5/S3/Entropy/Feedback/DemonIdentity.demon_average_divergence_eq`
- Dependency: [D5/S3/Entropy/MutualInformation](../MutualInformation.md)
