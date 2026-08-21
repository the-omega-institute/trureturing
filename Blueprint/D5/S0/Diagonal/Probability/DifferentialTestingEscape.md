# Differential-Testing Escape Formula

## Abstract

Uniform reference directories have the exact diagonal-mutation escape probability.

**Theorem 1.1 (Exact escape probability for diagonal mutants).**

$$\forall A, Y, [\operatorname{Fintype} A] [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y \to Y, \operatorname{directoryEscapeProbability}(f) = (1 - \frac{\operatorname{card}(\operatorname{Fix}(f))}{\operatorname{card}(Y)^{\operatorname{card}(A)}})^\operatorname{card}(A).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/DifferentialTestingEscape.directory_escape_probability_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source directory g : A -> Y^A is Lean's curried finite function A -> A -> Y. Its diagonal mutant is f(g(a)(a)), and escape means that this diagonal output is absent from every directory row.

The theorem uses the pinned uniform finite-PMF outer measure. The exact finite count is imported from D5.S0.Diagonal.EscapeCount.escaped_listing_card; the proof only bridges the source directory predicate and performs the cardinality-ratio arithmetic.

Pinned Mathlib was searched for PMF.toOuterMeasure_uniformOfFintype_apply, Fintype cardinality bridges, and ENNReal subtraction/division. No repository declaration packages this source-specific directory notation with the uniform outer-measure statement.

## References

- Truth anchor: `D5/S0/Diagonal/Probability/DifferentialTestingEscape.directory_escape_probability_exact`
- Dependency: [D5/S0/Diagonal/EscapeCount](../EscapeCount.md)
