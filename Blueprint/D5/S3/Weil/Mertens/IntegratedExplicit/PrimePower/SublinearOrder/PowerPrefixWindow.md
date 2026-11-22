# Balance the low and high frequencies at one cutoff

## Abstract

From Möbius prefixes to uniform prime-window bounds

**Theorem 1.1 (A signed prime-window bound from an ordinary prefix exponent).**

$$RH \Rightarrow \left(\forall beta \in \mathbb{R},\; \forall P \in \mathbb{R},\; \forall epsilon \in \mathbb{R},\; \left(\left(0 \le beta \land beta < 1\right) \land \left(\left(0 < P \land 0 < epsilon\right) \land \left(\forall N \in \mathbb{N},\; 1 \le N \Rightarrow \left|\operatorname{M}\left(N\right)\right| \le P \cdot N^{beta}\right)\right)\right) \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m^{\frac{2 + beta}{3} + epsilon} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerPrefixWindow.prime_window_mobius_of_power_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. Write θ(t) for the sum of log p over primes p ≤ t. The tail primeTail(x) is the integral of (θ(t)−t)/t² over t > x. The signed residual E(m,a,B) starts with the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a).

The zero series run over all nontrivial zeta-zero occurrences ρ, with each zero repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)). Both primitives use x > 0.

From E's starting expression subtract P(B)−P(a). For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) multiplied by −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract Pₙ(B)−Pₙ(a) multiplied by −μ(n), where μ is the Möbius function.

M(N) is the sum of μ(n) over 1≤n≤N. The hypothesis |M(N)|≤P N^β gives an absolute bound P q^β for every shorter prefix up to q=m+1. It controls the arithmetic and near-range terms. The trivial-root contribution has an additional factor 1+log q, absorbed by any fixed positive gap above β.

Let u=log x. For u≥q, Abel summation over degrees and the total variation of the damped mode give the low-bin cost O(P q^β(H+1)^(1+η)). Weighted sampling with the squared bin masses bounds the complement by O(q H^(η−1/2)). Both bounds are uniform over the full far range.

Set γ=2(1−β)/3 and H=floor(q^γ). Then H+1≤2q^γ and H≥q^γ/2. The latter inequality applies to the negative power in the tail. Both resulting exponents equal (2+β)/3+γη, and β<(2+β)/3<1. Choose η small enough to absorb the logarithm and fit the requested final slack.

Integrate the density with the factor exp(−(1/2−1/q)u) between log a and log B. The original endpoint gap is retained and vanishes when B=a. The constants are uniform in m, a and B. The argument places no lower bound on the size of the signed residual.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerPrefixWindow.prime_window_mobius_of_power_prefix`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedSpectrumCutoff](OmittedSpectrumCutoff.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerWindowDensity](PowerWindowDensity.md)
