# Signed summation and sampled root spectra

## Abstract

A linear remainder bound for the Möbius prime window

**Theorem 1.1 (A linear factor for every truncation order).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 2 \le T \land \left(0 < K \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m \cdot \left(a^{-\operatorname{s}\left(m\right)} - B^{-\operatorname{s}\left(m\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear.prime_window_mobius_linear_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E(m,a,B) be the signed residual. Start with the integral of the negative part of the prime-only tail divided by sqrt(x) on [a,B]. Subtract 2 log(B/a) and the ordinary spectral primitive at B minus its value at a. For 3 ≤ n ≤ m subtract a^(1/n−1/2)−B^(1/n−1/2) with coefficient −2μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m with 2n < m+1 subtract −μ(n) times the nth root primitive at B minus its value at a. Every primitive uses the same actual zero occurrences with multiplicity.

The identity μ(n) log n = −(μ∗Λ)(n) and the Chebyshev bound under RH give a logarithmic saving for the Möbius partial sums. Abel summation then bounds the signed sum of the trivial-zero responses by a constant times m. Each positive summand of the response increases with the degree, and the sum at the last degree is bounded by a harmonic number.

Write u=log x and q=m+1. For u≤q, the integrated Chebyshev estimate bounds each omitted centered root term at the target decay rate. For u≥q, group the samples u/n by unit intervals in 2u/q−u/n. The local mean square of a finite zero sum is bounded by the squares of its unit frequency bin masses. The Gaussian Fourier integral supplies a summable kernel in the bin difference. The signed unit zero count ensures square summability with analytic multiplicity.

The sample spacing is at least 1/q. On a unit interval the sampling bound controls the sum of the absolute values using the local integrals of the finite series and its derivative. Telescope over adjacent degrees to accommodate the varying coefficients. Their increments and the log-coordinate derivatives of those increments are bounded by 4/q and 1 times the reciprocal-norm majorant, respectively. Each band contributes at most a constant times q before its geometric weight, including the first band at zero exponent slack. Absolute convergence for each sample passes the bound to the full series.

The pointwise bound integrates over [log a, log B]. The rate s(m)=1/2−1/(m+1) is at least 1/6. The constant from integration is therefore uniform in m. Both sides vanish at B=a.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear.prime_window_mobius_linear_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/OmittedSpectrum](OmittedSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse](TrivialResponse.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusSingleLog](../RHMobiusSingleLog.md)
