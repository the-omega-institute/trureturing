# Not Eventually Periodic

## Abstract

The greedy expansion of one at the frontier base is not eventually periodic.

Suppose the digits repeated from some index on. The greedy remainders are confined to the unit interval and the base is expanding, so two sequences driven by those digits could not drift apart: the remainders would repeat with the same period. The reading of a code at the base is injective, so the codes would repeat too.

Reading those same codes at the conjugate then leaves the conjugate orbit only the values it took before the period closed, of which there are finitely many, so it would be bounded. It is not: from the fourth step onward it is past the escape threshold and the excess is multiplied at every step. The two sides cannot both hold.

Nothing here is proved for the first time. Every step is a statement landed separately, and the load-bearing one, the exact integer codes and the injectivity of their reading, is not mine. This module is where they meet.

**Theorem 1.1 (The expansion is not eventually periodic).**

$$\neg \left(\exists p \in N, N \in N,\; 0 < p \land \left(\forall n \in N,\; N \le n \Rightarrow \operatorname{beta13GreedyDigit}\left(n + p\right) = \operatorname{beta13GreedyDigit}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic.digits_not_eventually_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This settles the structural half of the frontier remark for this base. The measured half — that the count of normalised gap types grows with the window, was already carried elsewhere in the tree and is not restated here.

## References

- Truth anchor: `D5/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic.digits_not_eventually_periodic`
- Dependency: [D5/S0/Tower/NonPisotFrontier/BoundedForcesPeriodic](../NonPisotFrontier/BoundedForcesPeriodic.md)
- Dependency: [D5/S0/Tower/NonPisotFrontier/CollapseIsExpanding](../NonPisotFrontier/CollapseIsExpanding.md)
- Dependency: [D5/S0/Tower/NonPisotVerdict/ConjugateUnbounded](ConjugateUnbounded.md)
