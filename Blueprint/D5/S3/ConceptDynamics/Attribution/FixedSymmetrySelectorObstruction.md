# Fixed-Symmetry Obstruction to Equivariant Selection

## Abstract

One fixed-state symmetry without admissible fixed actions obstructs equivariant selection.

**Theorem 1.1 (No equivariant deterministic selector exists under a fixed-point-free stabilizer).**

$$\begin{gathered}\forall G, X, A: \operatorname{Type},\\{}[\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, X\right)], [\operatorname{MulAction}\left(G, A\right)],\\{}admissible: X \to \operatorname{Set}\left(A\right),\\{}(\exists x: X, g: G, \operatorname{smul}\left(g, x\right) = x \land (\forall a: A, a \in admissible\left(x\right) \Rightarrow \operatorname{smul}\left(g, a\right) \neq a)) \Rightarrow \neg \exists s: X \to A,\\{}(\forall y: X, s\left(y\right) \in admissible\left(y\right)) \land (\forall g: G, y: X, s\left(\operatorname{smul}\left(g, y\right)\right) = \operatorname{smul}\left(g, s\left(y\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FixedSymmetrySelectorObstruction.no_equivariant_selector_of_common_fixed_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single group element and state are quantified together. The element fixes that state but moves every action in its admissible set.

Any everywhere-admissible equivariant selector would choose an action in that set. Equivariance at the fixed state would force the chosen action to be fixed by the same element, contradicting the public premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FixedSymmetrySelectorObstruction.no_equivariant_selector_of_common_fixed_symmetry`
- Dependency: [D5/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction](StabilizerSelectorObstruction.md)
