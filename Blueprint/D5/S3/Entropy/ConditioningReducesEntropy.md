# Conditioning Reduces Entropy

## Abstract

For a finite normalized joint, conditioning on the first coordinate cannot increase the entropy of the second, in nats.

**Theorem 1.1 (Conditioning cannot increase entropy).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\\operatorname{conditionalEntropy}(p)\le\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ConditioningReducesEntropy.conditional_entropy_le_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional entropy is the marginal-weighted average entropy of the conditional slices. This theorem says that average does not exceed the entropy of the second marginal: conditioning on the first coordinate cannot increase the entropy of the second. The bound is on the average over slices, not on any individual slice; an individual conditional slice may well have higher entropy than the marginal.

This theorem is a composition of three frozen ingredients: the entropy chain rule, the mutual-information decomposition, and the nonnegativity of mutual information. It rewrites mutual-information nonnegativity with the two identities and closes the resulting linear inequality; nothing is re-proved and nothing is defined here.

The chain rule and the mutual-information decomposition need only nonnegativity. Normalization is forced here by exactly one ingredient: the nonnegativity of mutual information. The units are nats because shannonEntropy uses Real.log.

No equality condition is claimed: the case in which conditioning leaves entropy unchanged, namely independence, is not characterized here. The theorem says nothing about conditional mutual information and nothing beyond two coordinates.

## References

- Truth anchor: `D5/S3/Entropy/ConditioningReducesEntropy.conditional_entropy_le_marginal`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](ConditionalEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformationEntropy](MutualInformationEntropy.md)
