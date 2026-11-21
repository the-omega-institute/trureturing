# Two estimates on the same omitted root tail

## Abstract

A single-logarithm bound for the Möbius prime window

**Theorem 1.1 (One logarithm for every truncation order).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 2 \le T \land \left(0 < K \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m \cdot \left(1 + \log m\right) \cdot \left(a^{-\operatorname{s}\left(m\right)} - B^{-\operatorname{s}\left(m\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusSingleLog.prime_window_mobius_one_log_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E(m,a,B) be the signed residual. Start with the integral of the negative part of the prime-only tail divided by sqrt(x) on [a,B]. Subtract 2 log(B/a) and the ordinary spectral primitive at B minus its value at a. For 3 ≤ n ≤ m subtract the endpoint power difference of exponent 1/n − 1/2 with coefficient −2μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m with 2n < m+1 subtract −μ(n) times the nth root primitive at B minus its value at a. Every primitive uses the same actual zero occurrences with multiplicity.

The integrated arithmetic truncation contributes at most a constant times m at the target decay rate. The retained root spectra leave a centered trivial-zero error of size (1+log n) times x^(−1/2) per root. For an omitted degree n use both the actual-zero coefficient bound and the Schoenfeld bound integrated through the same centered tail. The latter uses the global Chebyshev bound on rooted arguments between one and the explicit threshold.

Write u=log x, q=m+1, λ=u/q and L=1+log m. After taking out the target decay, the two bounds supply the minimum of (1+2λ)² and L² times exp(−u(1/q−1/(2n))). For n at or above the first omitted degree this weight is at most exp(−λ(n−ceil(q/2))/q). Its sum is at most m and at most 1+q/λ for λ>0. The product with the minimum is at most 24mL. For odd m, the first omitted degree has zero exponent slack and contributes unit weight.

The pointwise bound integrates over [log a, log B]. The rate s(m)=1/2−1/(m+1) is at least 1/6. The constant from integration is therefore uniform in m. Both sides vanish at B=a.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusSingleLog.prime_window_mobius_one_log_of_rh`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/Schoenfeld](../../Cryptids/Schoenfeld.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow](RHMobiusWindow.md)
