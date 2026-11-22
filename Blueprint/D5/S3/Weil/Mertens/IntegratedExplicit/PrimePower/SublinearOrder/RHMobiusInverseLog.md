# A rate from the actual separation of the degree samples

## Abstract

An inverse logarithmic rate for the Möbius prime window

**Theorem 1.1 (Inverse logarithmic saving).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le \frac{K \cdot m}{\log (m + 1)} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusInverseLog.prime_window_mobius_inverse_log_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. Write θ(t) for the sum of log p over primes p ≤ t. The tail primeTail(x) is the integral of (θ(t)−t)/t² over t > x. The signed residual E(m,a,B) starts with the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a).

The zero series run over all nontrivial zeta-zero occurrences ρ, with each zero repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)). Both primitives use x > 0.

From E's starting expression subtract P(B)−P(a). For 3 ≤ n ≤ m subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) multiplied by −2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract Pₙ(B)−Pₙ(a) multiplied by −μ(n), where μ is the Möbius function.

Put q=m+1, u=log x, and L=1+log(q)/16. The zero-free half-plane estimate with θ=1/2 and α=1/4 bounds every ordinary Möbius prefix up to m by a constant times m^(3/4). Signed Abel summation with the omitted degrees gives a near-range coefficient of order exp(2L) m^(3/4) when u≤Lq. Since exp(2L)=exp(2) q^(1/8), this fits m/log q.

The same prefix bound controls the signed trivial-zero response by a constant times m^(3/4)(1+log m). The constant term and the loss from omitting μ(1) fit the same inverse logarithmic budget.

For u≥Lq the actual sample spacing bounds the omitted nontrivial spectrum by a constant times 1+q²/u+q^(7/8), after extracting exp(−(1/2−1/q)u). This coefficient is also of order m/log q. The signed arithmetic tail has the same coefficient.

Integrating the density estimate between log a and log B yields the endpoint power difference with a single threshold for all m≥2. Equal endpoints give zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusInverseLog.prime_window_mobius_inverse_log_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse](../LinearOrder/TrivialResponse.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSublinear](RHMobiusSublinear.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusEnergyPointwise](../../../../ZetaPntBounds/MobiusEnergyPointwise.md)
