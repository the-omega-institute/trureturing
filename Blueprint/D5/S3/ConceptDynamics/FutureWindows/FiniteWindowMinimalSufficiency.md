# Finite-Window Minimal Sufficiency

## Abstract

The realized finite orbit window is sufficient for every target in the window, and every simultaneously sufficient interface determines the entire window.

**Theorem 1.1 (The finite window is simultaneously sufficient and coarsest).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}q: X \to O, F: X \to X, n: \mathbb{N},\\{}(\forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(\operatorname{orbitTarget}\left(q, F, i\right)\right), \operatorname{canonicalTargetReadout}\left(\operatorname{finiteWindow}\left(q, F, n\right)\right)\right)) \land\\{}(\forall C: \operatorname{Type}, r: X \to C,\\{}(\forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{Refines}\left(\operatorname{orbitTarget}\left(q, F, i\right), r\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{finiteWindow}\left(q, F, n\right), r\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency.finite_future_window_minimal_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each index from zero through n, the canonical readout into the realized image of the corresponding orbit target factors through the canonical readout into the realized image of the whole finite window. This is target sufficiency with both interfaces restricted to their effective images.

Conversely, let r be any interface through which every raw orbit target in the window factors. The raw finite-window readout then factors through r. With Refines(coarse, fine) meaning that coarse factors through fine, this is exactly the coarsest factor-through property.

No inhabitedness, finiteness, or dynamical hypothesis is assumed. The finite dependent product includes horizon zero, and the effective-image clause remains valid for an empty state type.

## References

- Truth anchor: `D5/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency.finite_future_window_minimal_sufficiency`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency](../Sufficiency/FiniteWindowMinimalSufficiency.md)
