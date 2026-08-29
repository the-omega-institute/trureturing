# Singleton Axis Selection Obstruction

## Abstract

A globally fixed state cannot equivariantly select an axis when no axis is globally fixed.

**Theorem 1.1 (No canonical axis can be selected from a completely symmetric state).**

$$\begin{aligned}\forall G, X, A: \operatorname{Type},\\{}[\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, X\right)], [\operatorname{MulAction}\left(G, A\right)],\\{}\forall \omega: X,\\{}(\forall g: G, \operatorname{smul}\left(g, \omega\right) = \omega) \land (\forall a: A, \exists g: G, \operatorname{smul}\left(g, a\right) \neq a) \Rightarrow\\{}let XOmega: \operatorname{SubMulAction}\left(G, X\right) = (\{\omega\}, (\forall g: G, \operatorname{smul}\left(g, \omega\right) = \omega));\\{}\neg \exists sigma: XOmega \to A, (\forall g: G, x: XOmega, \operatorname{apply}\left(sigma, \operatorname{smul}\left(g, x\right)\right) = \operatorname{smul}\left(g, \operatorname{apply}\left(sigma, x\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SingletonAxisSelectionObstruction.no_equivariant_singleton_axis_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group act on states and axes. The named state is fixed by every group element, so its singleton is an invariant subaction.

If every axis is moved by some group element, an equivariant selector from that singleton would force its selected axis to be globally fixed, a contradiction.

The proof instantiates the frozen stabilizer-selector obstruction on the constructed singleton subaction. Repository and pinned-library searches found no theorem with this exact singleton domain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SingletonAxisSelectionObstruction.no_equivariant_singleton_axis_selector`
- Dependency: [D5/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction](StabilizerSelectorObstruction.md)
