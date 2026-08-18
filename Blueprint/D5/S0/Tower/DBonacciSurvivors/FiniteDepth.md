# Finite Depth

## Abstract

Every finite strict d-bonacci backward-survivor depth is nonempty, uniformly in the order.

The champion orbit is a two-branch cycle whose large phase sits exactly on the strict boundary. Its two coordinates are the base divided by the squared base less one, and the reciprocal of that same denominator. Both closure identities hold for any base whose squared value differs from one, so they carry no order-specific content; the order enters only through the Perron-root bounds.

**Theorem 1.1 (Every finite strict depth is nonempty at every order).**

$$\forall d \in N,\; 3 \le d \Rightarrow \left(\forall n \in N,\; \exists s \in \mathit{State},\; s \in \operatorname{backward}\left(d, \operatorname{strictSet}\left(d\right), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/FiniteDepth.strict_backward_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The perturbation budget is the smaller of the membership slack and the branch slack. The membership slack is positive exactly because every d-bonacci Perron root lies below two, and the branch slack is positive unconditionally.

**Theorem 1.2 (Order four separates).**

$$\left(\forall n \in N,\; \exists s \in \mathit{State},\; s \in \operatorname{backward}\left(4, \operatorname{strictSet}\left(4\right), n\right)\right) \land \operatorname{strictPermanent}\left(4\right) = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/FiniteDepth.four_finite_depths_nonempty_and_permanent_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The levels are open sets, so a nested intersection may be empty while every level is nonempty. The announced emptiness at a finite depth is therefore not a consequence of the permanent statement, and is refuted here.

**Theorem 1.3 (Order five separates).**

$$\left(\forall n \in N,\; \exists s \in \mathit{State},\; s \in \operatorname{backward}\left(5, \operatorname{strictSet}\left(5\right), n\right)\right) \land \operatorname{strictPermanent}\left(5\right) = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/FiniteDepth.five_finite_depths_nonempty_and_permanent_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Same separation at order five. Together with the order-two and order-three modules this settles the announced family.

## References

- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/FiniteDepth.five_finite_depths_nonempty_and_permanent_empty`
- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/FiniteDepth.four_finite_depths_nonempty_and_permanent_empty`
- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/FiniteDepth.strict_backward_nonempty`
- Dependency: [D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors](DBonacciPermanentSurvivors.md)
