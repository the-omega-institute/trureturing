# Finite-Window Minimal Sufficiency

## Abstract

Semiconjugate descents compose, and a finite orbit window is the coarsest readout sufficient for every observation in that window.

**Definition 1.1 (The finite window jointly records every orbit target through the horizon).**

$$\forall X, O: \operatorname{Type}, q: X \to O, F: X \to X, n: \mathbb{N},\\{}\operatorname{finiteWindow}\left(q, F, n\right) = \operatorname{jointTarget}\left((i: \operatorname{Fin}\left(n + 1\right) \mapsto \operatorname{orbitTarget}\left(q, F, \operatorname{val}\left(i\right)\right))\right).$$

*Formalization.* `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.finiteWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For q : X -> O, an endomorphism F, and a natural horizon n, the finite window is the joint target indexed by Fin(n + 1), whose component i is q observed after exactly i iterations of F.

**Lemma 1.2 (Semiconjugate descents compose).**

$$\begin{gathered}\forall X, B, C: \operatorname{Type},\\{}F: X \to X, Fbar: B \to B, Ftilde: C \to C,\\{}q: X \to B, r: B \to C,\\{}\operatorname{Semiconjugates}\left(q, F, Fbar\right) \Rightarrow \operatorname{Semiconjugates}\left(r, Fbar, Ftilde\right) \Rightarrow\\{}\operatorname{Semiconjugates}\left(r \circ q, F, Ftilde\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.descent_composes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose q carries the state update F to an update Fbar on an intermediate space, and r carries Fbar to an update Ftilde on a second space. Their composite r after q then carries F directly to Ftilde.

This transitivity statement is purely structural: it requires neither finite spaces nor inhabited spaces, and follows by substituting the first intertwining equality into the second.

**Theorem 1.3 (The finite orbit window is minimally sufficient).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\operatorname{Nonempty}\left(X\right), q: X \to O, F: X \to X, n: \mathbb{N},\\{}(\forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{orbitTarget}\left(q, F, i\right)\right), \operatorname{finiteWindow}\left(q, F, n\right)\right)) \land\\{}(\forall C: \operatorname{Type}, p: X \to C,\\{}(\forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{orbitTarget}\left(q, F, i\right)\right), p\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{finiteWindow}\left(q, F, n\right), p\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.finite_window_minimal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-window readout records q along the orbit from time zero through time n. For every index in that range, the canonical readout of the corresponding observed value factors through the whole window.

Conversely, if a candidate readout p is sufficient for every one of those canonical observed targets, the entire finite window factors through p. Under the convention that Refines(coarse, fine) means the coarse readout factors through the fine one, this makes the window the coarsest simultaneously sufficient readout.

The state space is assumed nonempty so that canonical target-image factorizations are available. No finiteness assumption is imposed on the state or observation types, and the conclusion includes the zero horizon n = 0.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.descent_composes`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.finiteWindow`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.finite_window_minimal_sufficiency`
- Dependency: [D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency](../Refinement/MultiTargetMinimalSufficiency.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](UniversalSufficiencyFactorization.md)
