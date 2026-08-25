# Symmetric Responsibility Allocation

## Abstract

A normalized equivariant allocation is uniform at a fully symmetric event.

**Theorem 1.1 (Symmetry forces equal responsibility).**

$$\begin{gathered}\forall n: \mathbb{N}, Event: \operatorname{Type},\\{}act: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right) \to Event \to Event,\\{}allocation: Event \to \operatorname{Fin}\left(n\right) \to \mathbb{R}, event: Event,\\{}(\forall i: \operatorname{Fin}\left(n\right), 0 \leq \operatorname{allocation}\left(event, i\right)) \land \\{}\sum_{i:\operatorname{Fin}\left(n\right)} \operatorname{allocation}\left(event, i\right) = 1 \land \\{}(\forall sigma: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), event': Event, i: \operatorname{Fin}\left(n\right), \operatorname{allocation}\left(act(sigma, event'), sigma(i)\right) = \operatorname{allocation}\left(event', i\right)) \land \\{}\operatorname{IsCompletelySymmetric}\left(act, event\right)\Rightarrow \\{}((\forall sigma: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), i: \operatorname{Fin}\left(n\right), \operatorname{allocation}\left(event, sigma(i)\right) = \operatorname{allocation}\left(event, i\right)) \land \\{}(\forall i: \operatorname{Fin}\left(n\right), \operatorname{allocation}\left(event, i\right) = \frac{1}{n})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetricResponsibilityAllocation.symmetric_responsibility_is_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivariance and complete symmetry first make the allocation invariant under every relabeling. Swaps then identify every pair of coordinates, and normalization fixes their common value at one divided by the number of labels.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetricResponsibilityAllocation.symmetric_responsibility_is_uniform`
- Dependency: [D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit](SymmetricEventNoUniqueCulprit.md)
