# A rate from the actual separation of the degree samples

## Abstract

An inverse double-logarithmic rate for the Möbius prime window

**Theorem 1.1 (Inverse double-logarithmic saving).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le \frac{K \cdot m}{1 + \log \log (m + 1)} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSpacing.prime_window_mobius_spacing_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. Write θ(t) for the sum of log p over primes p ≤ t. The tail primeTail(x) is the integral of (θ(t)−t)/t² over t > x. The signed residual E(m,a,B) starts with the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a).

The zero series run over all nontrivial zeta-zero occurrences ρ, with each zero repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)). Both primitives use x > 0.

From E's starting expression subtract P(B)−P(a). For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) multiplied by −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract Pₙ(B)−Pₙ(a) multiplied by −μ(n), where μ is the Möbius function.

The Chebyshev and floor convolutions reduce the Möbius prefix estimate to two ranges in the quotient. Choosing the quotient cutoff as the four-fifths power of the logarithm gives a one-fifth logarithmic saving, uniformly over prefixes. The signed trivial-root response inherits the saving by Abel summation.

Set L=(1+log log(m+1))/8. In the near range, with log x at most L(m+1), signed Abel summation costs at most a constant times exp(2L) m/log m after extracting the exponential in log x. This fits the stated coefficient.

In the far range set q=m+1 and u=log x. The actual coordinates u/n have separation at least u/q². In a unit window the separated-sample estimate uses the reciprocal of min(1,u/q²) on the value integral. The phase derivative carries a bin weight bounded by both q and a constant times one plus the absolute bin index.

Interpolate those two bounds to obtain a q^(7/8) derivative cost and square-summable bin mass proportional to (1+|k|)^(−5/8). Apply the same estimate to the adjacent coefficient increments and sum their variation. The weighted sum over unit windows then costs at most a constant times 1+q²/u+q^(7/8). With u≥Lq and L=(1+log log q)/8, this is bounded by a constant times m/(1+log log q).

For sufficiently large m these estimates give the explicit rate on the signed density. Integrating between log a and log B yields the stated power difference. The previous uniform linear estimate absorbs the finite set of smaller orders into the single constant. Equal endpoints give zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSpacing.prime_window_mobius_spacing_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear](../LinearOrder/RHMobiusLinear.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse](../LinearOrder/TrivialResponse.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusRate](RHMobiusRate.md)
