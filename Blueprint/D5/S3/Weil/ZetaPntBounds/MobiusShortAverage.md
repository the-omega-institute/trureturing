# Short averages of the first Riesz sum

## Abstract

Ordinary Möbius prefixes from a zero-free half-plane

**Theorem 1.1 (Prefix bounds up to any positive exponent slack).**

$$\forall b \in \mathbb{R},\; \left(\left(\frac{1}{2} \le b \land b < 1\right) \land \operatorname{Z}\left(b\right)\right) \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall N \in \mathbb{N},\; 1 \le N \Rightarrow \left|\operatorname{M}\left(N\right)\right| \le C \cdot N^{b + e}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusShortAverage.ordinary_mobius_prefix_of_zero_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The predicate Z(b) says that the Riemann zeta function is nonzero at every complex z with Re z>b and z≠1. The ordinary prefix M(N) is the sum of μ(n) over the integers 1≤n≤N.

For x=N and h=sqrt(x), difference the first Riesz sums at x+h and x and divide by h. The contribution of n≤N is M(N). There are at most h remaining integers, whose normalized weights lie in [0,1]. Since |μ(n)|≤1, the error is at most h.

The short secant of the Perron kernel has a single-denominator bound obtained by differentiating y^(s+1)/(s+1) in the positive real cutoff y. Bounding the two endpoint values separately gives an independent quadratic-denominator estimate.

The removable reciprocal of zeta is analytic in Re s>b and has growth O((1+|Im s|)^δ) on every fixed half-plane strictly to its right. The two short-kernel estimates interpolate to an integrable majorant proportional to (1+|Im s|)^(−1−δ). This controls the vertical integrals and the vanishing horizontal integrals during the line shift.

Choose δ=min(e/3,1/4) and move to Re s=b+δ. The kernel majorant contributes (x+h)^(b+δ)((x+h)/h)^(2δ), bounded by a constant times x^(b+2δ). The prefix error h is within the same target exponent. The RH case takes b=1/2, the classical exponent with arbitrary slack recorded by Soundararajan in equation (1) of Partial sums of the Möbius function.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusShortAverage.ordinary_mobius_prefix_of_zero_free`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Integral](../Mertens/Cryptids/WeightedStieltjes/Integral.md)
