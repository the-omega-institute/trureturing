# Strict Antitonicity of the Golden Displacement Series

## Abstract

A strict coordinate increase strictly lowers the golden displacement sum.

**Theorem 1.1 (A strict coordinate increase strictly lowers the sum).**

$$\forall s_1, w_1, s_2, w_2 \in \mathbb{R},\quad\operatorname{Summable}(\operatorname{dTerm}(s_1, w_1)) \land s_1 \leq s_2 \land w_1 \leq w_2 \land (s_1 < s_2 \lor w_1 < w_2) \Rightarrow\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s_2, w_2, n) < \sum_{n=0}^{\infty} \operatorname{dTerm}(s_1, w_1, n).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesStrictAntitone.golden_displacement_series_strict_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a parameter pair (s1,w1) where dTerm is summable. If both coordinates weakly increase and at least one strictly increases, then the sum at (s2,w2) is strictly smaller than the sum at (s1,w1).

The module exports the termwise parameter-order inequality as dTerm_le_of_parameters_le. At index two, the public identity goldenSubstStart(1)=2 gives nS(2)=4, so both real-power bases are strictly greater than one.

The base-greater-than-one real-power theorem makes the factor for the strictly increased coordinate strictly smaller. The other factor is weakly smaller and all factors are positive. Mathlib's Summable.tsum_lt_tsum_of_nonneg then promotes the strict inequality at index two and the termwise inequalities to a strict sum bound.

The implication form follows the earlier frozen non-strict companion and avoids a StrictAntiOn domain interface with redundant membership data. Only summability at the original parameter pair is assumed; the strict comparison theorem derives summability of the smaller term family internally.

The public termwise lemma is the usable authoritative declaration for new consumers. The earlier frozen non-strict companion keeps its own private copy: revoking a valid frozen node is an errata remedy, not an API-refactoring mechanism.

The theorem does not claim a quantitative gap, an equality characterization, a converse, strict decrease when both parameters are unchanged, or a finite sum value.

## References

- Truth anchor: `D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesStrictAntitone.golden_displacement_series_strict_antitone`
