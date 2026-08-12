# Conditional Entropy and Its Chain Rule

## Abstract

Finite conditional entropy in nats is the marginal-weighted entropy of conditional slices and satisfies the entropy chain rule.

**Definition 1.1 (Conditional entropy is marginal-weighted slice entropy).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\\operatorname{conditionalEntropy}(p):=\sum_{i}\operatorname{marginal}(p)(i)\operatorname{shannonEntropy}(\operatorname{conditional}(p,i)).\end{gathered}$$

*Formalization.* `D5/S3/Entropy/ConditionalEntropy.conditionalEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definitions of marginal and conditional come from D5/S3/Divergence/ChainRule; conditionalEntropy is the only new definition here. It is introduced because the chain rule and queued conditional results all consume it, not speculatively. The units are nats because shannonEntropy uses Real.log.

**Theorem 1.2 (Joint entropy obeys the chain rule).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\(\forall i, j, 0\le p(i,j)) \Rightarrow\\\operatorname{shannonEntropy}(p)=\operatorname{shannonEntropy}(\operatorname{marginal}(p))+\operatorname{conditionalEntropy}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ConditionalEntropy.entropy_chain_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint entropy splits into the marginal entropy plus the marginal-weighted average of the conditional slice entropies. This is the entropy-side counterpart of the frozen divergence chain rule.

The hypotheses are deliberately minimal: nonnegativity alone. Normalization is not required, even though a reader may expect a probability distribution.

When a marginal is zero, the conditional slice is a quotient by zero. That case is handled rather than excluded: nonnegativity forces every cell of such a slice to vanish, so the slice contributes nothing and the outer weight annihilates its term. No positivity is assumed anywhere.

On the nonnegative domain, the chain rule pins conditionalEntropy as the difference between two independently attested entropies. A wrong weight, a wrong slice association, or a slipped index that changes the aggregate would break the equality. This pin constrains the aggregate only: a corruption that leaves the aggregate unchanged on every nonnegative joint would not be caught.

This module proves no conditioning bound: the statement that conditioning cannot increase entropy is not proved here. It proves no conditional mutual information, no equality condition, and nothing beyond two coordinates.

## References

- Truth anchor: `D5/S3/Entropy/ConditionalEntropy.conditionalEntropy`
- Truth anchor: `D5/S3/Entropy/ConditionalEntropy.entropy_chain_rule`
- Dependency: [D5/S3/Divergence/ChainRule](../Divergence/ChainRule.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
