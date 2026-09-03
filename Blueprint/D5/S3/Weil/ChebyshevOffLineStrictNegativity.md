# Chebyshev Off-Line Strict Negativity

## Abstract

Every positive Chebyshev degree gives a strictly negative slack at a genuine off-line squared distance.

**Theorem 1.1 (Positive degrees are strictly negative off line).**

$$\begin{aligned}u_{a}(y) = \frac{y - a}{y + a}, W_{N,a}(y) = 1 - T_{N}(u_{a}(y))^{2},\\\forall N \in \mathbb{N}, a, x, \delta \in \mathbb{R},\\0 < N \land 0 < a \land 0 \le x \land \delta \neq 0 \land \delta^{2} < a \Rightarrow \kappa = \operatorname{arcosh}(\frac{a + \delta^{2}}{a - \delta^{2}}),\\u_{a}(-\delta^{2}) = -\operatorname{cosh}(\kappa) \land \kappa = 2 \cdot \operatorname{artanh}(\frac{\lvert\delta\rvert}{\sqrt{a}}),\\T_{N}(u_{a}(-\delta^{2})) = {-1}^{N} \cdot \operatorname{cosh}(N \cdot \kappa),\\W_{N,a}(-\delta^{2}) = -\operatorname{sinh}(N \cdot \kappa)^{2} < 0,\\u_{a}(x) \in [{-1}, 1] \land W_{N,a}(x) \in [0, 1].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ChebyshevOffLineStrictNegativity.chebyshev_off_line_strict_negativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive scale and a nonzero transverse displacement whose square lies below the scale, the compact coordinate is minus the hyperbolic cosine of the displayed rapidity.

The rapidity is twice artanh of the absolute normalized displacement. Mathlib's Chebyshev parity and hyperbolic evaluation identities then turn the slack into minus sinh squared, which is strict for positive degree.

For every nonnegative input, the same compactification lies in the closed unit interval and its Chebyshev slack lies in [0,1]. The Lean module separately records equality at zero degree and zero displacement.

## References

- Truth anchor: `D5/S3/Weil/ChebyshevOffLineStrictNegativity.chebyshev_off_line_strict_negativity`
- Dependency: [D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity](CayleyLaguerre/ChebyshevSlackPositivity.md)
