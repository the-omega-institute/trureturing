# Boolean Reversal Has Exact Period Two

## Abstract

Boolean negation gives every state exact period two.

**Theorem 1.1 (Boolean reversal has exact period two).**

$$\forall b \in \mathbb{B},\ \operatorname{minimalPeriod}(\operatorname{not}, b) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/BooleanReversal.boolean_reversal_has_minimal_period_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each Boolean state b, applying negation twice returns b, while a single negation never fixes b. Hence the minimal positive return time is exactly two.

This closes qdo-v1 corollary/38.4, atom qdo-residual-8581f6063c025dfe2404a2a8064e7c04c67fe3091ca9821043e697a82f20e73e.

Pinned Mathlib supplies the periodic-point minimal-period API and Bool.not_ne_self. Loogle returned no declaration for the query Function.minimalPeriod = 2, and repository search found no equivalent theorem.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/BooleanReversal.boolean_reversal_has_minimal_period_two`
