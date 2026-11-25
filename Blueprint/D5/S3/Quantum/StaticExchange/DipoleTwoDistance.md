# Two distances identify two dipole response coefficients

## Abstract

For a fixed finite spectrum with positive scales and nonnegative weights, two ordered positive distances identify the coefficients of the second and fourth responses whenever two distinct scales have positive weight.

**Definition 1.1 (Normalized radial profile).**

Lean statement: `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.profile`

*Formalization.* `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At s the profile q equals (1+s+s²/3) exp(−s). Its value at zero is one.

**Theorem 1.2 (Strict ordering at two scales).**

$$0<x<y \land 0<a<b \Rightarrow q(xa)q(yb) < q(xb)q(ya)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.profile_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<b the ratio q(bt)/q(at) strictly decreases for positive t. Its denominator stays positive. After canceling positive exponential and denominator factors, the derivative has the sign of minus t(b−a) times a polynomial with positive coefficients in a, b and t. Multiplying the resulting ratio inequality at x and y by the two positive denominators gives the displayed minor.

**Definition 1.3 (Spectral moment response).**

Lean statement: `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.moment`

*Formalization.* `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite list of scales gᵢ and weights pᵢ the order-k response at t is the sum of pᵢ gᵢᵏ q(tgᵢ). Write U and V for orders two and four.

**Theorem 1.4 (Strict determinant and uniqueness of the coefficients).**

$$\begin{aligned}&0<x<y \land (\forall i,0 \le p(i) \land 0<g(i)) \land (\exists i,j:0<p(i) \land 0<p(j) \land g(i)<g(j))\\&\Rightarrow U(x)V(y) < V(x)U(y) \land \mathrm{Injective}((s,t) \mapsto (sU(x)+tV(x),sU(y)+tV(y)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.finite_spectral_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every spectral scale is positive, all weights are nonnegative and two distinct scales have positive weight. For any 0<x<y the signed determinant has the displayed strict ordering. Thus the two real linear coefficients in sU+tV are uniquely determined by the readings at x and y.

Expand twice the positive difference V(x)U(y)−U(x)V(y) as a double sum over pairs of scales. In each summand the difference of squared scales and the corresponding difference of profile products have the same sign. Their product is multiplied by nonnegative weights. A positively weighted pair of unequal scales contributes strictly. Eliminating each coefficient using the nonzero determinant gives injectivity.

## References

- Truth anchor: `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.finite_spectral_separation`
- Truth anchor: `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.moment`
- Truth anchor: `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.profile`
- Truth anchor: `D5/S3/Quantum/StaticExchange/DipoleTwoDistance.profile_minor`
