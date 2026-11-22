# A double-logarithmic saving in the truncation order

## Abstract

An explicit rate for the Möbius prime-window remainder

**Theorem 1.1 (The same window and decay exponent).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le \frac{K \cdot m}{\sqrt{1 + \log \log (m + 1)}} \cdot \left(a^{-\operatorname{s}\left(m\right)} - B^{-\operatorname{s}\left(m\right)}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusRate.prime_window_mobius_quantitative_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed residual E(m,a,B) is the integral of the negative part of the prime-only tail divided by sqrt(x) on [a,B], with 2 log(B/a) and the endpoint difference of the ordinary zero primitive subtracted. For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) with coefficient −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract the nth root primitive difference with coefficient −μ(n). Actual zero occurrences retain their analytic multiplicities.

The Chebyshev and floor convolutions reduce the Möbius prefix estimate to two ranges in the quotient. Choosing the quotient cutoff as the four-fifths power of the logarithm gives a one-fifth logarithmic saving, uniformly over prefixes. The signed trivial-root response inherits the saving by Abel summation.

Set L=(1+log log(m+1))/8. In the near range, with log x at most L(m+1), signed Abel summation costs at most a constant times exp(2L) m/log m after extracting the exponential in log x. This fits the stated coefficient.

In the far range, with log x at least L(m+1), split the actual unit frequency bins at height of order L². The low-bin mass grows at most as the fourth root of the cutoff. The square root of the squared high-bin mass is bounded by the inverse fourth root. Sum the geometric degree weights in the first part and use Gaussian local sampling in the second. Both parts give a bound proportional to m/sqrt(L).

For sufficiently large m these estimates give the explicit rate on the signed density. Integrating between log a and log B yields the stated power difference. The previous uniform linear estimate absorbs the finite set of smaller orders into the single constant. Equal endpoints give zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusRate.prime_window_mobius_quantitative_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear](../LinearOrder/RHMobiusLinear.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse](../LinearOrder/TrivialResponse.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/ArithmeticResponse](ArithmeticResponse.md)
