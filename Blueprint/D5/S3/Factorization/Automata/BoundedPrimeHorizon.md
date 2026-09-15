# Two-Boundary Observation of a Prime Register

## Abstract

Both guard distances, rather than current legality alone, determine the exact finite-horizon state.

The bounded runner records whether the entire requested word was legal. At horizon H, compare all words of total length at most H, including the empty word.

**Theorem 1.1 (The exact two-boundary profile).**

$$\forall a, H \in \mathbb{N}, \forall e, f: \operatorname{Fin}(a + 1), (\forall w: \operatorname{List}(Bool), \operatorname{length}(w) \leq H \Rightarrow \operatorname{accepts}(a, e, w) = \operatorname{accepts}(a, f, w)) \iff \operatorname{close}(a, H, e, f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/BoundedPrimeHorizon.finite_horizon_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two live states have equal responses to every such word exactly when the displayed profiles agree. Necessity uses repeated multiplication and division. Sufficiency is induction over the word: first-step guards agree, and successful successors have equal profiles at H-1. Mixed paths, underflow and overflow are all covered.

**Theorem 1.2 (Every profile is realized and counted).**

$$\forall a, H \in \mathbb{N}, \operatorname{Surjective}((q: \operatorname{Option}(\operatorname{Fin}(a + 1))) \mapsto \operatorname{map}(\operatorname{code}(a, H), q)) \land (\forall q, r: \operatorname{Option}(\operatorname{Fin}(a + 1)), (\forall w: \operatorname{List}(Bool), \operatorname{length}(w) \leq H \Rightarrow \operatorname{observed}(a, q, w) = \operatorname{observed}(a, r, w)) \iff \operatorname{map}(\operatorname{code}(a, H), q) = \operatorname{map}(\operatorname{code}(a, H), r)) \land \operatorname{card}(\operatorname{Option}(\operatorname{Fin}(\operatorname{min}(a, 2 \times H) + 1))) = \operatorname{min}(a, 2 \times H) + 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/BoundedPrimeHorizon.profile_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete code collapses only the central interval. It is surjective onto Fin(min(a,2H)+1), and its kernel is exactly the response kernel. The separate rejection point remains visible on the empty word. This is not a claim that a fixed-H quotient updates autonomously for arbitrarily many later steps.

## References

- Truth anchor: `D5/S3/Factorization/Automata/BoundedPrimeHorizon.finite_horizon_kernel`
- Truth anchor: `D5/S3/Factorization/Automata/BoundedPrimeHorizon.profile_classification`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](../../../S0/Automata/TypedPartialDFAOOverBase.md)
