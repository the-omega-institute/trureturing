# Finite-Window Stability Is Descent

## Abstract

A finite observation window is stable exactly when its update preserves fibers and descends uniquely to the realized window image.

**Lemma 1.1 (The depth-one window kernel is the next window kernel).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}q: X \to O, F: X \to X, n: \mathbb{N},\\{}\operatorname{depthOneKernel}\left(\operatorname{finiteWindow}\left(q, F, n\right), F\right) = \operatorname{finiteWindowKernel}\left(q, F, n + 1\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent.depth_one_finite_window_eq_next_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The depth-n window records the observations at times zero through n. Its depth-one kernel requires equality both on that current window and on the same window after one update.

The two overlapping windows therefore require equality exactly at times zero through n + 1. Their depth-one kernel is the finite-window kernel at the next horizon, for arbitrary state and observation types.

**Theorem 1.2 (Finite-window stability is equivalent to congruence and descent).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}q: X \to O, F: X \to X, n: \mathbb{N},\\{}\operatorname{ListTFAE}\left({[\operatorname{finiteWindowKernel}\left(q, F, n\right) = \operatorname{finiteWindowKernel}\left(q, F, n + 1\right), \operatorname{InterfaceCongruence}\left(\operatorname{finiteWindow}\left(q, F, n\right), F\right), \operatorname{EffectiveDescent}\left(\operatorname{finiteWindow}\left(q, F, n\right), F\right)]}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent.finite_window_stability_congruence_descent_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stability at horizon n says that equality of observations through time n already determines equality through time n + 1. This is equivalent to the update preserving every fiber of the depth-n window readout.

The same condition is equivalent to a unique descended update on the realized image of that window, commuting with the original state update. Thus kernel stability, interface congruence, and effective descent are three forms of one condition.

The equivalence holds without finiteness or nonemptiness assumptions on the state and observation types, including the zero horizon.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent.depth_one_finite_window_eq_next_window`
- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent.finite_window_stability_congruence_descent_tfae`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](DeterministicInterfaceEquivalence.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency](../Sufficiency/FiniteWindowMinimalSufficiency.md)
