# Best Safe Abstraction

## Abstract

The Galois-derived transformer is safe and pointwise most precise among safe abstractions.

**Theorem 1.1 (The Galois-derived transformer is the best safe abstraction).**

$$\forall X, A: Type, \operatorname{Preorder}\left(A\right), \alpha: \operatorname{Set}\left(X\right) \to A, \gamma: A \to \operatorname{Set}\left(X\right), F: X \to X,\\{}\operatorname{GaloisConnection}\left(\alpha, \gamma\right) \Rightarrow let Fbest: A \to A := \alpha \circ \operatorname{image}\left(F\right) \circ \gamma,\\{}(\forall a: A, \operatorname{image}\left(F, \gamma(a)\right) \subseteq \gamma(Fbest(a))) \land\\{}\forall Gsharp: A \to A, (\forall a: A, \operatorname{image}\left(F, \gamma(a)\right) \subseteq \gamma(Gsharp(a))) \Rightarrow \forall a: A, Fbest(a) \leq Gsharp(a).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Adjunction/BestSafeAbstraction.best_safe_abstraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public canonical transformer first concretizes an abstract state, takes the direct image under the concrete process, and abstracts the result.

The unit of the Galois connection proves safety. Applying the adjunction to any other safe transformer proves that the canonical transformer is pointwise below it, hence at least as precise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Adjunction/BestSafeAbstraction.best_safe_abstraction`
