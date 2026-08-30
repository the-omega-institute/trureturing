# The Logarithmic Contrapositive Margin

## Abstract

A logarithmic margin turns fast-implies-long into short-implies-slow.

**Theorem 1.1 (The quarter-short witnesses are eventually slow).**

$$\forall Witness: Type, implements: N \to Witness \to Prop, runningTime: N \to Witness \to N, timeBound: N \to N, boundedNameCost: N \to Witness \to N, \forall error: N \to R, (\operatorname{IsBigO}\left(error, atTop, \operatorname{lambda}\left(\operatorname{typed}\left(n, N\right), \operatorname{log}\left(\operatorname{castReal}\left(n\right)\right)\right)\right) \land \forall n: N, u: Witness, \operatorname{IsFastWitness}\left(implements, runningTime, timeBound, n, u\right) \Rightarrow \operatorname{HasLongName}\left(boundedNameCost, error, n, u\right)) \Rightarrow \exists n_{0}: N, \forall n: N, n \ge n_{0} \Rightarrow (\frac{\operatorname{castReal}\left(n\right)}{2} - error\left(n\right) > \frac{\operatorname{castReal}\left(n\right)}{4} \land \forall u: Witness, \operatorname{HasShortName}\left(implements, boundedNameCost, n, u\right) \Rightarrow \operatorname{IsSlowWitness}\left(runningTime, timeBound, n, u\right)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/NamingRate/LogarithmicMargin.logarithmic_error_eventually_leaves_quarter_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public predicates retain the source's witness semantics. A fast witness is valid and runs within timeBound(n); a long name reaches n / 2 - error(n); a short witness is valid and has boundedNameCost at most n / 4; and a slow witness exceeds timeBound(n).

Clause (i), fast implies long, is the public premise. Clause (ii) is the eventual conclusion: the strict n / 2 - error(n) > n / 4 margin holds and every quarter-short valid witness is slow. Assuming a short witness were not slow would make it fast, contradicting clause (i) across the displayed margin.

Pinned Mathlib supplies Real.isLittleO_log_id_atTop. The source uses base-two logarithms, while Lean's Real.log is natural logarithm; their positive constant-factor conversion gives the same big-O class. The helper restricts the real asymptotic to natural inputs and obtains the explicit quarter-margin.

## References

- Truth anchor: `D5/S0/Asymptotics/NamingRate/LogarithmicMargin.logarithmic_error_eventually_leaves_quarter_margin`
