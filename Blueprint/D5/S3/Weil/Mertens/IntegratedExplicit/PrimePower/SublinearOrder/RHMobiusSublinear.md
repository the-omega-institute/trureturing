# One left threshold for every accuracy

## Abstract

A uniformly sublinear Möbius prime-window remainder

**Theorem 1.1 (The same window and decay exponent).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; 2 \le T \land \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists M \in \mathbb{N},\; 2 \le M \land \left(\forall m \in \mathbb{N},\; M \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le epsilon \cdot m \cdot \left(a^{-\operatorname{s}\left(m\right)} - B^{-\operatorname{s}\left(m\right)}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSublinear.prime_window_mobius_sublinear_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed residual E(m,a,B) is the integral of the negative part of the prime-only tail divided by sqrt(x) on [a,B], with 2 log(B/a) and the endpoint difference of the ordinary zero primitive subtracted. For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) with coefficient −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract the nth root primitive difference with coefficient −μ(n). Actual zero occurrences retain their analytic multiplicities.

The Chebyshev and floor convolutions for μ(n) log n give a signed identity for the Möbius partial sum times log n. Split at a fixed fraction of the cutoff. The power saving for the Chebyshev error bounds the initial part and Abel summation bounds the complementary part. The resulting little-o estimate also bounds all prefixes at the common scale. Abel summation then controls the increasing logarithmic trivial-root response.

The signed Chebyshev truncation tail has a logarithmic saving after integrating on the original positive cutoff. For log x at most L(m+1), the integrated Chebyshev root term and its arithmetic main term are each decreasing in the omitted degree. Signed summation gives the required saving on their difference.

For log x at least L(m+1), choose a finite set of unit frequency bins so the complementary squared bin masses have arbitrarily small sum. Gaussian local sampling bounds that complement, including the variation in coefficients between adjacent degrees. The finite set of bins satisfies the geometric weight sum bound 1+(m+1)²/log x. Choose L and then the minimum degree to make both contributions small.

The eventual sign of the prime-only tail fixes the left threshold before the accuracy and the truncation order are chosen. Integrate over [log a, log B] with s(m)=1/2−1/(m+1)≥1/6. Equal endpoints give zero on both sides.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSublinear.prime_window_mobius_sublinear_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/OmittedSpectrum](../LinearOrder/OmittedSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/ArithmeticResponse](ArithmeticResponse.md)
