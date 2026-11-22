# Balance the damped degree prefix against the high-frequency tail

## Abstract

A three-quarter exponent for the signed RH prime window

**Theorem 1.1 (The signed prime-window bound with arbitrary exponent slack).**

$$RH \Rightarrow \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right)\right| \le K \cdot m^{\frac{3}{4} + epsilon} \cdot \left(a^{\frac{1}{m + 1} - \frac{1}{2}} - B^{\frac{1}{m + 1} - \frac{1}{2}}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusThreeQuarters.prime_window_mobius_three_quarters_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH denotes Mathlib RiemannHypothesis. The window discrepancy is the integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a). The tail primeTail(x) integrates (θ(t)−t)/t² over t>x, where θ(t) sums log p over primes p≤t.

The zero series use all actual nontrivial zero occurrences, each repeated according to its analytic multiplicity. The ordinary primitive P(x) is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)), for x>0.

The signed residual E(m,a,B) subtracts P(B)−P(a) from the window discrepancy and then subtracts both signed correction sums. For 3≤n≤m, the first sum uses −2 μ(n)n²/((n−1)(n−2)) multiplied by a^(1/n−1/2)−B^(1/n−1/2). For 2≤n≤m and 2n<m+1, the second sum uses −μ(n) multiplied by Pₙ(B)−Pₙ(a).

Write q=m+1 and η=min(ε/3,1/12). The ordinary Möbius prefix exponent 1/2+η controls the arithmetic and near-range terms. The normalized omitted density for u≥q has three costs: q^(1/2+η)(H+1)^(1/2+η), (H+1)^(1+η), and q H^(η−1/2).

Take H=floor(q^(1/2)). The upper bound for H+1 controls the first two costs. The lower bound H≥q^(1/2)/2 controls the negative power. They are bounded by constants times q^(3/4+2η), independent of u.

Integrate the density against exp(−(1/2−1/q)u) between log a and log B. This gives the original endpoint gap for every allowed real pair a≤B, with value zero at equality.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusThreeQuarters.prime_window_mobius_three_quarters_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/OmittedPrefixSpectrum](OmittedPrefixSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerWindowDensity](PowerWindowDensity.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusShortAverage](../../../../ZetaPntBounds/MobiusShortAverage.md)
