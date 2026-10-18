# Real-Power Elasticity Monotonicity

## Abstract

A real-power certificate makes the binary Renyi elasticity transform monotone for every real n at least one.

The parameter n is real. The monotonicity domain is the open interval (0,1), and n = 1 is included. Powers with the exponents n, n minus one and twice n use Real.rpow; the displayed square factors use natural exponent two. The definitions are total real functions, while the sign and derivative arguments below use strictly positive bases.

**Definition 1.1 (Power-ratio transform).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), \operatorname{T}\left(n, r\right) = \frac{1 - (r)^{n}}{1 + (r)^{n}}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T compares the difference and sum of one and the nth power of r.

**Definition 1.2 (Logarithmic derivative factor).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), \operatorname{A}\left(n, r\right) = \frac{n \cdot (r)^{n - 1} \cdot \left(1 - (r)^{2}\right)}{1 - (r)^{2 \cdot n}}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This factor will equal t times the logarithmic derivative of T(n,(1-t)/(1+t)).

**Definition 1.3 (Bias-times-transform factor).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), \operatorname{B}\left(n, r\right) = \frac{1 - r}{1 + r} \cdot \operatorname{T}\left(n, r\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bias coordinate corresponding to r is (1-r)/(1+r).

**Definition 1.4 (Elasticity transform).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), \operatorname{F}\left(n, r\right) = \frac{\operatorname{A}\left(n, r\right) - \operatorname{B}\left(n, r\right)}{1 + \operatorname{B}\left(n, r\right)}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F is the real-power expression for the elasticity of minus the derivative of binary Renyi entropy in bias coordinates.

**Definition 1.5 (Real-power sign certificate).**

$$\forall (n: \mathbb{R}), \forall (z: \mathbb{R}), \operatorname{J}\left(n, z\right) = n - 1 - \left(n + 1\right) \cdot z + \left(n + 1\right) \cdot (z)^{n} - \left(n - 1\right) \cdot (z)^{n + 1}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four-term auxiliary function controls the sign of A's derivative.

The derivative certificate is J₁(n,z)=(n+1)(-1+n z^(n-1)-(n-1)z^n). It records the first derivative of J on positive bases.

**Theorem 1.6 (Derivative of J).**

$$\forall (n: \mathbb{R}), \forall (z: \mathbb{R}), (0 < z) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{J}\left(n\right), \operatorname{J1}\left(n, z\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-power derivative identity requires only a positive base.

**Theorem 1.7 (Second derivative of J).**

$$\forall (n: \mathbb{R}), \forall (z: \mathbb{R}), (0 < z) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{J1}\left(n\right), n \cdot \left((n)^{2} - 1\right) \cdot (z)^{n - 2} \cdot \left(1 - z\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J1_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second derivative factors into a parameter sign and positive-base factors.

**Theorem 1.8 (Nonnegativity of J from its curvature).**

$$\forall (n: \mathbb{R}), \forall (z: \mathbb{R}), (0 \le n \cdot \left((n)^{2} - 1\right)) \Rightarrow \left((z \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow 0 \le \operatorname{J}\left(n, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J and its first derivative vanish at one. Nonnegative second derivative therefore gives J >= 0. The condition includes both n >= 1 and -1 < n < 0.

The explicit derivative expressions are A₁(n,r)=n r^(n-2) J(n,r^2)/(1-r^(2n))^2, B₁(n,r)=-2 T(n,r)/(1+r)^2-2n((1-r)/(1+r))r^(n-1)/(1+r^n)^2, and F₁(n,r)=A₁(n,r)/(1+B(n,r))-(1+A(n,r))B₁(n,r)/(1+B(n,r))^2. These functions separate the derivative signs used in the positive and negative order regimes.

**Theorem 1.9 (Derivative of A for nonzero real n).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), (n \ne 0) \Rightarrow \left((r \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{A}\left(n\right), \operatorname{A1}\left(n, r\right), r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.A_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The denominator is nonzero for every nonzero n and 0 < r < 1. Both positive and negative real parameters use the same derivative proof.

**Theorem 1.10 (Derivative of B).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), (r \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{B}\left(n\right), \operatorname{B1}\left(n, r\right), r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.B_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The power-ratio derivative and product rule apply to every real n.

**Theorem 1.11 (Derivative of F).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), (n \ne 0) \Rightarrow \left((r \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow \left((0 < 1 + \operatorname{B}\left(n, r\right)) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{F}\left(n\right), \operatorname{F1}\left(n, r\right), r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.F_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient rule applies when n is nonzero and 1+B is positive. The positive- and negative-order consumers establish that sign separately.

**Theorem 1.12 (Positivity of the power-ratio transform).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), (1 \le n) \Rightarrow \left((r \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow 0 < \operatorname{T}\left(n, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.T_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least one and 0 < r < 1, the nth power of r lies strictly between zero and one. Thus the numerator and denominator of T are both positive.

**Theorem 1.13 (Derivative of the power-ratio transform).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), (0 < r) \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{T}\left(n\right), \frac{-2 \cdot n \cdot (r)^{n - 1}}{(1 + (r)^{n})^{2}}, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.T_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only r > 0 is required; n is any real number. The proof directly uses Mathlib's real-power derivative and the quotient rule.

**Theorem 1.14 (Factoring the denominator of A).**

$$\forall (n: \mathbb{R}), \forall (r: \mathbb{R}), (0 < r) \Rightarrow \operatorname{A}\left(n, r\right) = \frac{n \cdot (r)^{n - 1} \cdot \left(1 - (r)^{2}\right)}{\left(1 - (r)^{n}\right) \cdot \left(1 + (r)^{n}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.A_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive base, the real-power product law identifies r to twice n with the square of r to n. Factoring the difference of squares gives this identity without a restriction on n.

**Theorem 1.15 (Monotonicity of the elasticity transform).**

$$\forall (n: \mathbb{R}), (1 \le n) \Rightarrow \operatorname{MonotoneOn}\left(\operatorname{F}\left(n\right), \operatorname{Ioo}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.monotoneOn_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real n at least one, F(n,r) is nondecreasing on (0,1). The proof in fact establishes a strictly positive derivative on that interval.

The sign certificate is the four-term real-power function $\operatorname{J}\left(n, z\right) = n - 1 - \left(n + 1\right) \cdot z + \left(n + 1\right) \cdot (z)^{n} - \left(n - 1\right) \cdot (z)^{n + 1}$. Its first derivative is (n+1)(-1+n z^(n-1)-(n-1)z^n), and its second derivative is n(n^2-1) z^(n-2)(1-z). The second derivative is nonnegative on (0,1). On each interval [z,1] with z > 0, derivative monotonicity and J'(1)=J(1)=0 first give J' <= 0 and then J >= 0. No differentiability at zero is needed when 1 <= n < 2.

Differentiating A gives A'(r)=n r^(n-2) J(r^2)/(1-r^(2n))^2, hence A' >= 0. The derivative of B is -2 T/(1+r)^2 - 2n((1-r)/(1+r))r^(n-1)/(1+r^n)^2, which is strictly negative. Since A and B are positive, F'=A'/(1+B)-(1+A)B'/(1+B)^2 is strictly positive. At n=1 the J term vanishes, but the B term remains strictly negative.

The consumer is the alpha-at-least-two clause of C. Hirche, Renyi Bounds on Information Combining, ISIT 2020, arXiv:2004.14408v1, Conjecture IV.18. This certificate supplies the real-order one-variable inequality; it does not assert a result for orders below two.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.A`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.A_eq`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.A_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.B`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.B_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.F`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.F_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J1_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.J_nonneg`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.T`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.T_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.T_pos`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone.monotoneOn_F`
