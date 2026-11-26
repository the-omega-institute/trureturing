# Sum the omitted degrees with their exponential damping

## Abstract

The order exponent past square-root spacing

**Theorem 1.1 (The signed residual at very late starting points).**

$$RH \Rightarrow \left(\forall d \in \mathbb{R},\; \left(\frac{1}{2} \le d \land d \le 1\right) \Rightarrow \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(\left(T \le a \land a \le B\right) \land \left(m + 1\right)^{1 + d} \le \operatorname{log}\left(a\right)\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m^{1 - d + epsilon} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusVeryLate.prime_window_mobius_very_late_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. The window discrepancy is the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a). The tail primeTail(x) integrates (θ(t)−t)/t² over t>x, where θ(t) sums log p over primes p≤t.

The zero series use all actual nontrivial zero occurrences, each repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)), for x>0.

The signed residual E(m,a,B) subtracts P(B)−P(a) from the window discrepancy and then subtracts both signed correction sums. For 3≤n≤m, the first sum uses −2 μ(n)n²/((n−1)(n−2)) multiplied by a^(1/n−1/2)−B^(1/n−1/2). For 2≤n≤m and 2n<m+1, the second sum uses −μ(n) multiplied by Pₙ(B)−Pₙ(a).

Write q=m+1 and u=log x. For 1/2≤d≤1 the integration interval satisfies u≥q^(1+d)≥q^(3/2). The arithmetic tail uses a geometric sum from q to 2q−1 and an exponential bound for higher degrees.

The actual root density of each omitted degree has a coefficient bound of order (1+log q)². Summing its degree weights contributes at most 1+q²/u. The trivial roots have an extra damping factor exp(−u/q) relative to the common rate, so their contribution fits the same bound.

On the given window 1+q²/u≤2q^(1−d). The logarithms are absorbed by positive exponent slack. Integrating against exp(−(1/2−1/q)u) gives the original endpoint gap. At d=1 this yields exponent ε, and at B=a both sides vanish.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusVeryLate.prime_window_mobius_very_late_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/LateArithmeticTail](LateArithmeticTail.md)
