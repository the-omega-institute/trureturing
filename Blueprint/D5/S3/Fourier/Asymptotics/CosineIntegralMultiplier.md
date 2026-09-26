# The Cosine-Integral Fourier Multiplier

## Abstract

The actual cosine-integral tail has an exact Fourier transform in complex Lebesgue L2 at every positive scale.

**Definition 1.1 (The spatial kernel).**

$$\forall c \in \mathbb{R}, x \in \mathbb{R},\; \operatorname{q}\left(c, x\right) = \operatorname{ofReal}\left(2 \cdot \operatorname{Ci}\left(c \cdot \left|x\right|\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function q(c,x) is the complex embedding of 2 Ci(c|x|). Ci is the existing real function sin(x)/x minus the integral of sin(t)/t^2 over t>x. For x>0 this tail integral converges absolutely. The definition gives a value at zero, whose choice does not affect its L2 class.`D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral``D5/L/Fourier/nist2026cosineintegral`

**Definition 1.2 (The frequency function).**

$$\forall c \in \mathbb{R}, xi \in \mathbb{R},\; \operatorname{m}\left(c, xi\right) = \operatorname{ofReal}\left(\operatorname{ite}\left(\frac{c}{2 \cdot \pi} \le \left|xi\right|, \frac{-1}{\left|xi\right|}, 0\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.m` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real value -1/|xi| is embedded into the complex numbers when |xi| is at least c/(2 pi); the value is zero below this threshold. Here ite selects its second argument when its first argument holds, and its third argument otherwise. For c>0 the support is unbounded and avoids a neighborhood of zero.

**Theorem 1.3 (Every positive real scale).**

$$\forall c \in \mathbb{R},\; 0 < c \Rightarrow \left(\operatorname{MemLp}\left(\operatorname{q}\left(c\right), 2, \operatorname{Lebesgue}\left(\right)\right) \land \left(\operatorname{MemLp}\left(\operatorname{m}\left(c\right), 2, \operatorname{Lebesgue}\left(\right)\right) \land \operatorname{FourierL2}\left(\operatorname{class}\left(\operatorname{q}\left(c\right)\right)\right) = \operatorname{class}\left(\operatorname{m}\left(c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real c>0, both q(c) and m(c) belong to complex L2 of Lebesgue measure on the real line. FourierL2 denotes the actual Fourier linear isometry equivalence with phase exp(-2 pi i x xi); class denotes the almost-everywhere quotient class constructed using the established membership. The theorem proves equality of these Lp elements. No integrability or transform identity is assumed.

On a finite positive frequency interval [a,b], reflect the integrable function -1/xi to the negative interval. Its inverse Fourier integral is 2(Ci(2 pi a|x|)-Ci(2 pi b|x|)) for x nonzero. Integration by parts in the convergent sine tail establishes the finite-interval cosine identity. The two complex exponential terms combine to twice the real cosine.

Fourier duality against Schwartz functions and the injective embedding of L2 into tempered distributions identify the finite-band integral with the actual inverse L2 transform. The spatial and frequency tails both have squared L2 norm 4 pi/c. The spatial identity follows from the cosine-integral Gram formula. Sending the upper frequency cutoff to infinity therefore gives actual L2 convergence on both sides, and continuity of the Fourier isometry gives the asserted equality.`D5/S3/Fourier/Asymptotics/CosineIntegralGram.result`

Changing values at zero or at either threshold does not change the quotient classes. In angular frequency zeta=2 pi xi the same multiplier is -2 pi/|zeta| for |zeta|>=c, and zero otherwise. The weighted integral-operator norm bound requires its own operator representation and estimate; it is not asserted here. No mixed process limit is asserted.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralGram.result`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.m`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.q`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.result`
- Dependency: [D5/S3/Fourier/Asymptotics/CosineIntegralGram](CosineIntegralGram.md)
