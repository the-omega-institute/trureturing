# The Bivariate Admissible-Word Equation

## Abstract

Admissible-word bookkeeping obeys its bivariate self-substitution equation.

**Theorem 1.1 (The word series splits into its two substituted branches).**

$$(\operatorname{bookkeepingSeries}: \operatorname{Degree} \to \operatorname{Cardinal}) = (degree: \operatorname{Degree} \mapsto \operatorname{skipBranchSeries}(degree) + \operatorname{takeBranchSeries}(degree)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BivariateWordSeries.bookkeeping_series_self_functional_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficients count finite binary words with no adjacent occupied positions by a pair of bookkeeping exponents. A canonical nonempty word is either a single occupied position, a skipped position followed by a nonempty word, or an occupied position followed by a forced skip and a nonempty word. Including the empty word makes this a disjoint two-branch decomposition.

Skipping the lowest position sends an exponent pair (a, b) to (b, a+b), which is the monomial substitution (u, v) to (v, uv). Occupying it sends (a, b) to (a+b+1, a+2b), which is multiplication by u after the substitution (u, v) to (uv, uv^2). The Lean proof constructs an explicit equivalence on every coefficient fiber and uses pinned Mathlib's cardinality-of-equivalence and cardinality-of-sum declarations. Mathlib supplies that general machinery but has no declaration for this admissible-word equation, so the combinatorial bijection is new proof content rather than a wrapper.

## References

- Truth anchor: `D5/S1/Recurrence/BivariateWordSeries.bookkeeping_series_self_functional_equation`
