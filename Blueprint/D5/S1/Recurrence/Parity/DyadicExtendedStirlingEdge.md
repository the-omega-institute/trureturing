# The binary-weight row edge

## Abstract

Binary-weight support and the factorial edge of the literal rational extended Stirling array.

All indices range over the natural numbers, including zero. T is the literal rational scalar array of D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock; it is not defined by its edge values. The function wt is binary popcount from D5/S1/Digit/DyadicRowPolynomialRecurrence. The function a is exactly A284005 from D5/S1/Digit/KurkovWeightProductBinomial, with a(0)=1 and a(1)=2. Casts, division and array values in the edge identity are rational; factorial and its argument are natural.

**Theorem 1.1 (The support bound).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{wt}\left(n\right) + 2 < k \Rightarrow \operatorname{T}\left(n, k\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

Strong induction on the row uses its exact dyadic decomposition n=2^g(n)*(2*h(n)+1). The parent is strictly smaller, and wt(n)=wt(h(n))+1. Both parent columns in the block law are outside their support, so they vanish.

**Theorem 1.2 (The complete row-edge identity).**

$$\forall n \in \mathbb{N},\; \operatorname{T}\left(n, \operatorname{wt}\left(n\right) + 2\right) = \frac{\operatorname{rat}\left(\operatorname{a}\left(n\right)\right)}{\operatorname{rat}\left(\operatorname{factorial}\left(1 + \operatorname{wt}\left(n\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a358612-row-edge` (proved) by `D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a358612-row-edge","declaration_gid":"D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2024). *OEIS A358612: extended Stirling numbers from binary row indices*. URL: <https://oeis.org/A358612>.

*Commentary.*

This is the all-natural-row conjectured formula T(n,A000120(n)+2)=A341392(n) from A358612, using the A341392 definition A284005(n)/(1+A000120(n))!. The initial row is checked separately. At positive n the upper parent term vanishes by support; the remaining block coefficient is (wt(h(n))+2)^g(n). The source-owner identity a(n)=(wt(h(n))+2)^(g(n)+1)*a(h(n)) and factorial recursion finish the induction. The support statement is proved, not assumed. No bounded row restriction or integrality hypothesis is added. The scalar PARI source is used only on positive columns; the formal zero-column extension never enters the induction. The dyadic block law is a reused live prerequisite, without a separate block-problem settlement in this document. This statement does not assert integrality or any other A358612 conjecture.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.result`
- Truth anchor: `D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.support`
- Dependency: [D5/S1/Digit/KurkovWeightProductBinomial](../../Digit/KurkovWeightProductBinomial.md)
- Dependency: [D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock](DyadicExtendedStirlingBlock.md)
