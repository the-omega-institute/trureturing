# Polynomial Complexity and Subshift Hausdorff Dimension

## Abstract

Polynomial factor complexity forces the associated prefix-language subshift to have Hausdorff dimension zero.

Let x be a one-sided infinite word over a finite nontrivial discrete alphabet. Its prefix-language subshift consists of the infinite words whose prefix of every length occurs somewhere as a factor of x.

**Definition 1.1 (The subshift is defined by the factor language of the base word).**

$$X_x = \{y : \forall n\in \mathbb{N}, P_n(y)\in F_x(n)\}$$

*Formalization.* `D5/S1/Words/Complexity/SubshiftHausdorffDimension.wordSubshift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor set uses natural starting positions and represents a length-n word as a function on Fin n. No two-sided extension is built into this definition.

**Theorem 1.2 (The base word belongs to its subshift).**

$$x\in X_x$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftHausdorffDimension.self_mem_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix of x occurs at starting position zero, so the defining language condition holds at every length.

**Theorem 1.3 (The subshift is invariant under the one-step shift).**

$$y\in X_x \Rightarrow s(y)\in X_x$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftHausdorffDimension.wordSubshift_shift_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shifted prefix of length n is obtained by deleting the first letter from a length-(n+1) prefix. Its occurrence therefore moves one natural position to the right inside the base word.

**Theorem 1.4 (Positive-dimensional Hausdorff measures vanish).**

$$(\forall n\in \mathbb{N}, \operatorname{card}(F_x(n)) \leq C \times (n+1)^{k}) \land 0 < d \Rightarrow \operatorname{muH}(d, X_x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftHausdorffDimension.hausdorffMeasure_wordSubshift_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth n, the allowed factors index a finite cover by prefix cylinders. Each cylinder has extended diameter at most 2^(-n), while the number of cylinders is bounded by C(n+1)^k.

For every d > 0, polynomial growth times the exponential factor ((1/2)^d)^n tends to zero. Mathlib's finite-cover liminf estimate then forces the d-dimensional Hausdorff measure to vanish.

**Theorem 1.5 (Polynomial-complexity subshifts have dimension zero).**

$$(\forall n\in \mathbb{N}, \operatorname{card}(F_x(n)) \leq C \times (n+1)^{k}) \Rightarrow \operatorname{dimH}(X_x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftHausdorffDimension.dimH_wordSubshift_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing at every positive exponent places the Hausdorff dimension below every positive nonnegative real. Nonnegativity supplies the reverse bound.

**Theorem 1.6 (The golden subshift has dimension zero).**

$$\operatorname{dimH}(X_g) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/SubshiftHausdorffDimension.dimH_goldenSubshift_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact golden factor count is n+1. The formal bridge maps each Fin-indexed factor to its list representation with List.ofFn and uses injectivity to preserve finite-set cardinality.

This document does not identify the prefix-language set with an orbit closure, and it does not establish closedness, uncountability, or perfectness.

## References

- Truth anchor: `D5/S1/Words/Complexity/SubshiftHausdorffDimension.dimH_goldenSubshift_eq_zero`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftHausdorffDimension.dimH_wordSubshift_eq_zero`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftHausdorffDimension.hausdorffMeasure_wordSubshift_eq_zero`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftHausdorffDimension.self_mem_wordSubshift`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftHausdorffDimension.wordSubshift`
- Truth anchor: `D5/S1/Words/Complexity/SubshiftHausdorffDimension.wordSubshift_shift_invariant`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter](../../../S0/Asymptotics/MetricGeometry/GreenClassDiameter.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
