# Golden Germ Next Exponent Pattern

## Abstract

Every consecutive golden beta gap is phi or phi-squared, while beta eight, beta nine, and the mixed-weight census below beta seven are explicit.

**Theorem 1.1 (All beta gaps and the next finite exponent census).**

$$\begin{aligned}\forall v\in \mathbb{N}, (\operatorname{o5Beta}(v + 1) - \operatorname{o5Beta}(v) = \varphi \lor \operatorname{o5Beta}(v + 1) - \operatorname{o5Beta}(v) = \varphi^{2}) \land\\\operatorname{o5Beta}(8) = \varphi^{6} \land\\\operatorname{o5Beta}(9) = \varphi^{6} + \varphi^{2} \land\\\operatorname{o5Beta}(7) < \operatorname{o5Beta}(8) < \operatorname{o5Beta}(9) \land\\\forall a, b\in \mathbb{N},\\a \times \varphi^{2} + b \times \varphi^{3} \leq \operatorname{o5Beta}(7) \iff (b = 0 \land a \leq 5) \lor (b = 1 \land a \leq 4) \lor (b = 2 \land a \leq 2) \lor (b = 3 \land a \leq 1).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermNextExponentPattern.golden_germ_next_exponent_pattern` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural mode, the floor increment between consecutive golden multiples is one or two. Unfolding the frozen o5Beta definition converts these two integer cases into consecutive beta gaps equal to phi or phi-squared.

The floor values at nine and ten times phi give beta eight equal to phi to the sixth power and beta nine equal to phi-sixth plus phi-squared. The frozen fourth-order census supplies beta seven. Together these values prove the two strict inequalities and the complete natural-pair census below beta seven; the pair a equal to one and b equal to three is the boundary equality.

This theorem advances the next exponent-accounting boundary in the golden Euler germ extraction ladder of OACTC parts 580 and 581. It classifies exponent gaps and finite candidate weights only. It does not assert factor cancellation, an all-order extraction, analytic continuation, O-5, or the Riemann Hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermNextExponentPattern.golden_germ_next_exponent_pattern`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus](GoldenGermFourthOrderExponentCensus.md)
