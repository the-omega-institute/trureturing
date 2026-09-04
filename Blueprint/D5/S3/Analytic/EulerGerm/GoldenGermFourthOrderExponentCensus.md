# Golden Germ Fourth-Order Exponent Census

## Abstract

The next two golden Euler exponents have explicit phi-polynomial values, and the mixed phi-squared and phi-cubed weights through beta six form a finite census.

**Theorem 1.1 (Beta six and beta seven delimit the finite fourth-ledger candidate census).**

$$\begin{aligned}\operatorname{o5Beta}(6) = 2 \times \varphi^{4},\\\operatorname{o5Beta}(7) = \varphi^{5} + \varphi^{3},\\\operatorname{o5Beta}(5) < \operatorname{o5Beta}(6) < \operatorname{o5Beta}(7),\\\varphi^{5} < \operatorname{o5Beta}(6) \land \varphi^{5} < \operatorname{o5Beta}(7),\\\forall a, b\in \mathbb{N},\\a \times \varphi^{2} + b \times \varphi^{3} \leq \operatorname{o5Beta}(6) \iff (b = 0 \land a \leq 5) \lor (b = 1 \land a \leq 3) \lor (b = 2 \land a \leq 2) \lor (b = 3 \land a = 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus.golden_germ_fourth_order_exponent_census` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact floor values at six, seven, and eight times the golden ratio give beta five equal to phi to the fifth power, beta six equal to twice phi to the fourth power, and beta seven equal to phi to the fifth plus phi-cubed. In particular beta five is below beta six, which is below beta seven, and both new exponents lie above the phi-fifth threshold.

The displayed alternatives enumerate every natural pair whose mixed weight a phi-squared plus b phi-cubed is at most beta six. The boundary pair a equal to two and b equal to two is retained because its weight is exactly twice phi to the fourth power. The frozen third-order ledger is the direct predecessor; its local floor and power lemmas are private, so this module reuses the public o5Beta definition and reconstructs those arithmetic evaluations locally.

This finite ledger advances the open exponent-accounting boundary on the golden Euler germ extraction staircase used in OACTC parts 580 and 581. It only identifies candidate weights for selecting signed fourth-order zeta factors. It does not assert fourth-order cancellation, a wider continuation or summability region, O-5, or the Riemann Hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus.golden_germ_fourth_order_exponent_census`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger](GoldenGermThirdOrderLedger.md)
