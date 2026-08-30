# Logarithmic Error Leaves a Linear Margin

## Abstract

A logarithmic error eventually leaves a strict quarter-scale linear margin.

**Theorem 1.1 (The logarithmic remainder is eventually below the linear gap).**

$$\forall error: N \to R, \operatorname{IsBigO}\left(error, atTop, \operatorname{lambda}\left(\operatorname{typed}\left(n, N\right), \operatorname{log}\left(\operatorname{castReal}\left(n\right)\right)\right)\right) \Rightarrow \exists n_{0}: N, \forall n: N, n \ge n_{0} \Rightarrow \frac{\operatorname{castReal}\left(n\right)}{2} - error\left(n\right) > \frac{\operatorname{castReal}\left(n\right)}{4}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/NamingRate/LogarithmicMargin.logarithmic_error_eventually_leaves_quarter_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let error be any real-valued sequence on the natural numbers. If it is bounded by a constant multiple of log n at infinity, then from some index onward n / 2 - error(n) is strictly greater than n / 4.

Pinned Mathlib supplies Real.isLittleO_log_id_atTop. The proof restricts this real asymptotic to natural inputs, composes it with the stated big-O premise, and takes an explicit one-eighth bound.

This deposit formalizes exactly theorem 4.5 clause 3: the logarithmic remainder is eventually dominated by the quarter-scale linear margin. The neighboring fast-witness and short-witness clauses are separate ledger atoms and are not restated here.

## References

- Truth anchor: `D5/S0/Asymptotics/NamingRate/LogarithmicMargin.logarithmic_error_eventually_leaves_quarter_margin`
