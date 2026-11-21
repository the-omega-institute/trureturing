# One real threshold for every truncation order

## Abstract

The prime-only window at an arbitrary Möbius truncation order

**Theorem 1.1 (Deterministic and spectral contributions on the same window).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 2 \le T \land \left(0 < K \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m \cdot \left(1 + \log m\right)^{2} \cdot \left(a^{-\operatorname{s}\left(m\right)} - B^{-\operatorname{s}\left(m\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow.prime_window_mobius_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E(m,a,B) be the signed residual. Start with the integral of the negative part of the prime-only tail divided by sqrt(x) on [a,B]. Subtract 2 log(B/a) and the ordinary spectral primitive at B minus its value at a. For 3 ≤ n ≤ m subtract the endpoint power difference of exponent 1/n − 1/2 with coefficient −2μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m with 2n < m+1 subtract −μ(n) times the nth root primitive at B minus its value at a. Every primitive uses the same actual zero occurrences with multiplicity.

A finite Möbius truncation produces an arithmetic error whose density constant grows at most linearly in m. The centered transform of the complete tail gives coefficient n/(2j(n+2j)) for the jth trivial zero. Its sum is bounded by a harmonic number, including at rooted argument one. Splitting the actual nontrivial zeros by height at n bounds the omitted spectral density by a constant times (1+log n)² x^(1/(2n) − 1/2), within the target decay when 2n ≥ m+1.

Summing gives the uniform density factor m(1+log m)². Integration over [log a, log B] preserves both endpoints. The rate s(m)=1/2 − 1/(m+1) lies above or at 1/6, so integration keeps one constant for all m. The inequality includes B=a.

At m=10 the eighth and ninth deterministic terms vanish. The tenth term has coefficient −25/9 and the fifth-root primitive enters at the same scale, with remaining decay exponent 9/22.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow.prime_window_mobius_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff](MobiusCutoff.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusWindowTransfer](MobiusWindowTransfer.md)
