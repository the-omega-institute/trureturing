# Mutual Information as an Entropy Balance

## Abstract

Finite mutual information in nats decomposes into marginal and joint Shannon entropies, yielding entropy subadditivity.

**Theorem 1.1 (Mutual information is the entropy balance).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\(\forall i, j, 0\le p(i,j)) \Rightarrow\\\operatorname{mutualInformation}(p)=\operatorname{shannonEntropy}(\operatorname{marginal}(p))+\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j)))-\operatorname{shannonEntropy}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformationEntropy.mutual_information_eq_entropy_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decomposition is the identity tying this bucket's two definitions together: mutual information equals the sum of the two marginal entropies minus the joint entropy. Both marginal entropies use the repository's single marginal definition; the second applies it to the coordinate-swapped joint. The units are nats because the definitions use Real.log. This module defines nothing of its own.

This theorem is the general pin. The sibling module D5/S3/Entropy/MutualInformationProduct constrains the mutual-information definition only on product joints, and is blind to a reference that agrees there but differs on correlated joints. The decomposition holds for every admissible joint, including correlated joints, so it constrains the definition exactly where the product-law identity could not. It does not by itself make the mutual-information definition beyond question; it establishes this specific consistency relation with the imported entropy and marginal definitions.

The hypotheses are deliberately minimal: the decomposition needs only nonnegativity of the joint, and normalization is not required. This asymmetry matters because a reader may expect both results to require a probability distribution. Zero-mass cells are handled by cases without assuming positive marginals. In particular, a cell may vanish while both of its marginals are positive; that case is covered, not excluded.

**Theorem 1.2 (Joint entropy is subadditive).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\\operatorname{shannonEntropy}(p)\le\operatorname{shannonEntropy}(\operatorname{marginal}(p))+\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformationEntropy.entropy_subadditive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entropy subadditivity is derived, not independently proven. The proof rewrites the decomposition against the frozen mutual_information_nonneg theorem; nothing about nonnegativity is re-proved. Normalization enters only here, because it is required to invoke that frozen nonnegativity theorem.

The conclusion is H(X,Y) <= H(X) + H(Y) for the two marginals of a finite joint, in nats. It does not give an equality condition for subadditivity: no characterization of when H(X,Y) = H(X) + H(Y), equivalently independence, is claimed. It says nothing about conditional entropy or conditional mutual information, and nothing beyond two coordinates.

## References

- Truth anchor: `D5/S3/Entropy/MutualInformationEntropy.entropy_subadditive`
- Truth anchor: `D5/S3/Entropy/MutualInformationEntropy.mutual_information_eq_entropy_sub`
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformation](MutualInformation.md)
