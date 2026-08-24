# Finite-Window Minimal Sufficiency

## Abstract

Semiconjugate descents compose, and a finite orbit window is the coarsest readout sufficient for every observation in that window.

**Lemma 1.1 (Semiconjugate descents compose).**

$$\begin{gathered}\forall X, B, C: \operatorname{Type},\\{}F: X \to X, Fbar: B \to B, Ftilde: C \to C,\\{}q: X \to B, r: B \to C,\\{}\operatorname{Semiconjugates}\left(q, F, Fbar\right) \Rightarrow \operatorname{Semiconjugates}\left(r, Fbar, Ftilde\right) \Rightarrow\\{}\operatorname{Semiconjugates}\left(r \circ q, F, Ftilde\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.descent_composes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose q carries the state update F to an update Fbar on an intermediate space, and r carries Fbar to an update Ftilde on a second space. Their composite r after q then carries F directly to Ftilde.

This transitivity statement is purely structural: it requires neither finite spaces nor inhabited spaces, and follows by substituting the first intertwining equality into the second.

**Theorem 1.2 (The finite orbit window is minimally sufficient).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}\operatorname{Nonempty}\left(X\right), q: X \to O, F: X \to X, n: \mathbb{N},\\{}(\forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{orbitTarget}\left(q, F, i\right)\right), \operatorname{finiteWindow}\left(q, F, n\right)\right)) \land\\{}(\forall C: \operatorname{Type}, p: X \to C,\\{}(\forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{orbitTarget}\left(q, F, i\right)\right), p\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{finiteWindow}\left(q, F, n\right), p\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.finite_window_minimal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-window readout records q along the orbit from time zero through time n. For every index in that range, the canonical readout of the corresponding observed value factors through the whole window.

Conversely, if a candidate readout p is sufficient for every one of those canonical observed targets, the entire finite window factors through p. Under the convention that Refines(coarse, fine) means the coarse readout factors through the fine one, this makes the window the coarsest simultaneously sufficient readout.

The state space is assumed nonempty so that canonical target-image factorizations are available. No finiteness assumption is imposed on the state or observation types, and the conclusion includes the zero horizon n = 0.

**Lemma 1.3 (Empty states obstruct zero-window refinement).**

$$\begin{gathered}q: \emptyset \to Unit, F: \emptyset \to \emptyset,\\{}\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{orbitTarget}\left(q, F, 0\right)\right), \operatorname{finiteWindow}\left(q, F, 0\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.nonempty_state_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the state type to be Empty, the observation type to be Unit, and the horizon to be zero. The finite-window carrier Fin 1 to Unit is inhabited by the constant unit-valued window.

The corresponding orbit target has empty image because there is no state. A refinement factor would map the inhabited window carrier into that empty target image, which is impossible. This is the obstruction excluded by the nonempty-state assumption.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.descent_composes`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.finite_window_minimal_sufficiency`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.nonempty_state_is_necessary`
- Dependency: [D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency](../Refinement/MultiTargetMinimalSufficiency.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](UniversalSufficiencyFactorization.md)
