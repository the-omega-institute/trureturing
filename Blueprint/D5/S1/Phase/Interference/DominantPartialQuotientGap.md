# Dominant Partial-Quotient Gap

## Abstract

A dominant term leaves a nonnegative reverse-triangle gap below a finite complex sum.

**Theorem 1.1 (A dominant term leaves a lower gap).**

$$\forall S, a, k,\ k \in S \land \sum _{i \in S\setminus\{k\}} |a_{i}| \le |a_{k}| \Rightarrow 0 \le |a_{k}|-\sum _{i \in S\setminus\{k\}} |a_{i}| \le |\sum _{i \in S} a_{i}|$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DominantPartialQuotientGap.dominant_partial_quotient_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite support for complex terms a_i and let k belong to S. If the norm of a_k is at least the sum of the norms of every other supported term, then the difference is nonnegative and is a lower bound for the norm of the full sum. Strict dominance therefore makes the displayed gap positive.

Pinned Mathlib was searched before proving. `norm_sub_norm_le` supplies the reverse triangle inequality and `norm_sum_le` bounds the norm of the erased remainder by its sum of norms. `Finset.sum_erase_add` only restores the selected term. The declaration is a thin named wrapper over those results.

The nearest repository theorem, `SeatTowerConsequences.dominant_term_gap_bound`, is an unconditional integer leading-term bound. It does not provide this selected finite complex family, the dominance premise, or the nonnegative-gap result. No dominant partial-quotient identification is asserted here.

**Theorem 1.2 (The positive gap is attained by an explicit family).**

$$\{2, -1\}: 1 < 2 \land 0 < 2-1 = |2-1| = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DominantPartialQuotientGap.strict_dominance_positive_gap_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Fin 2 take the complex family (2, -1), support both indices, and select the first. The remainder norm sum is one, strictly below the dominant norm two. The resulting gap is one and the full sum also has norm one, so the lower bound is positive and attained rather than vacuous.

## References

- Truth anchor: `D5/S1/Phase/Interference/DominantPartialQuotientGap.dominant_partial_quotient_gap`
- Truth anchor: `D5/S1/Phase/Interference/DominantPartialQuotientGap.strict_dominance_positive_gap_example`
