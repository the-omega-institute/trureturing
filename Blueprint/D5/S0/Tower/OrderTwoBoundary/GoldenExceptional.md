# Golden Exceptional

## Abstract

The general champion formula vanishes at order two, so order two lies outside its range rather than inside it by a small margin.

The general champion value divides the golden minimal polynomial by the squared base less one. At the golden ratio that numerator is exactly zero, so the formula returns zero while the order-two tower's own champion value is strictly positive. The exclusion of order two from the general statement is therefore structural, not a rounding concession.

**Theorem 1.1 (Order two lies outside the general formula).**

$$\left(\varphi^{2} - \varphi - 1 = 0 \land \operatorname{championValue}\left(\varphi\right) = 0\right) \land \left(0 < \mathit{goldenThreshold} \land \operatorname{championValue}\left(\varphi\right) \ne \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/OrderTwoBoundary/GoldenExceptional.order_two_is_outside_the_general_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same vanishing numerator also makes the finite-depth argument degenerate at order two: the constraint that the predecessor coordinate stay at or below the reciprocal base reads as positivity of that numerator, and at the golden ratio it holds with equality rather than strictly.

## References

- Truth anchor: `D5/S0/Tower/OrderTwoBoundary/GoldenExceptional.order_two_is_outside_the_general_formula`
- Dependency: [D5/S0/Tower/Champions/GoldenSurvivorTubes](../Champions/GoldenSurvivorTubes.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](../DBonacciGeneral/ChampionValue.md)
