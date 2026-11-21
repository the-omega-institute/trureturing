# Defant's Conjecture 4.1

## Abstract

The rational prime 3 has a 2-powerful friend in Defant's ring of radicand −11.

**Definition 1.1 (Radicands).**

$$K = \left\{-163, -67, -43, -19, -11, -7, -3, -2, -1\right\}$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.K` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

Defant restricts the conjecture to these nine negative radicands.

**Definition 1.2 (Quadratic integer ring).**

$$\forall d \in \mathbb{Z},\; \operatorname{R}\left(d\right) = \operatorname{QuadraticAlgebra}\left(\mathbb{Z}, (\mathrm{if} d \bmod 4 = 1 \mathrm{then} (d-1)/4 \mathrm{else} d), (\mathrm{if} d \bmod 4 = 1 \mathrm{then} 1 \mathrm{else} 0)\right)$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.R` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

In the integral basis, the generator is the square root of d when d is 2 or 3 modulo 4, and half the sum of one and that root when d is 1 modulo 4. The two parameters a and b encode the equation for the square of the generator as a plus b times the generator. The remainder and division in the parameters are integer operations.

**Definition 1.3 (Nonzero elements).**

$$\forall d \in \mathbb{Z},\; \operatorname{Nonzero}\left(d\right) = \{z: \operatorname{R}\left(d\right) \mid z \ne 0\}$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.Nonzero` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

The divisor sum, index, and friendship are defined on nonzero ring elements.

**Definition 1.4 (Absolute value).**

$$\forall d \in \mathbb{Z}, z \in \operatorname{R}\left(d\right),\; \operatorname{absoluteValue}\left(z\right) = \sqrt{(QuadraticAlgebra.norm\left(z\right): \mathbb{R})}$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.absoluteValue` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

The norm is the integer obtained by multiplying an element by its conjugate. The absolute value is its real square root.

**Definition 1.5 (Half-open sector).**

$$\forall d \in \mathbb{Z},\; \operatorname{A}\left(d\right) = \{z: \operatorname{R}\left(d\right) \mid (\mathrm{if} (d = -1) \lor (d = -3) \mathrm{then} (0 < z.re) \land (0 \le z.im) \mathrm{else} (0 < z.im) \lor ((z.im = 0) \land (0 < z.re)))\}$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.A` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

The real and imaginary projections here are integral coordinates. The coordinate tests give arguments in [0, π/2) for d = −1, [0, π/3) for d = −3, and [0, π) otherwise.

**Definition 1.6 (Power sum of sector divisors).**

$$\forall d \in \mathbb{Z}, n \in \mathbb{Z}, z \in \operatorname{Nonzero}\left(d\right),\; \operatorname{delta}\left(n, z\right): \mathbb{R} = \sum^{\mathrm{f}}_{x: \operatorname{R}\left(d\right)} (\mathrm{if} (x \mid z.val) \land (x \in \operatorname{A}\left(d\right)) \mathrm{then} \operatorname{absoluteValue}\left(x\right)^{n} \mathrm{else} 0)$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.delta` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

Definition 2.1 permits integer exponents. The terms range over the ring, with zero weight outside the actual divisors in the half-open sector. The positive definite multiplicative norm bounds the coordinates of these divisors by the norm of the input, so the sum has finite support.

**Definition 1.7 (Normalized abundancy index).**

$$\forall d \in \mathbb{Z}, n \in \mathbb{N}, z \in \operatorname{Nonzero}\left(d\right),\; \operatorname{I}\left(n, z\right) = \frac{\operatorname{delta}\left((n: \mathbb{Z}), z\right)}{\operatorname{absoluteValue}\left(z.val\right)^{n}}$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.I` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

Definition 2.2 uses positive natural exponents. The numerator casts n to an integer exponent and the denominator uses its natural power.

**Definition 1.8 (Powerful friendship).**

$$\forall d \in \mathbb{Z}, n \in \mathbb{N}, z \in \operatorname{Nonzero}\left(d\right), w \in \operatorname{Nonzero}\left(d\right),\; (\operatorname{PowerfullyFriendly}\left(n, z, w\right)) \Leftrightarrow ((\operatorname{I}\left(n, z\right) = \operatorname{I}\left(n, w\right)) \land (\operatorname{absoluteValue}\left(z.val\right) \ne \operatorname{absoluteValue}\left(w.val\right)))$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.PowerfullyFriendly` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

Two nonzero inputs are n-powerfully friendly when the normalized indices agree and the absolute values differ.

**Definition 1.9 (Rational prime power).**

$$\forall (d: \mathbb{Z}) (p: \mathbb{N}) (k: \mathbb{N}) (hp: Nat.Prime\left(p\right)), \operatorname{primePower}\left(d, p, k, hp\right).val = ((p^{k}: \mathbb{N}): \operatorname{R}\left(d\right))$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.primePower` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

Take the natural power and cast it into the quadratic ring. Primality of p implies the power is nonzero, giving the subtype witness.

**Definition 1.10 (Conjecture 4.1).**

$$claim = (\forall d \in \mathbb{Z},\; (d \in K) \Rightarrow (\forall (p: \mathbb{N}) (hp: Nat.Prime\left(p\right)) (k: \mathbb{N}), (0 < k) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\forall z \in \operatorname{Nonzero}\left(d\right),\; \neg\operatorname{PowerfullyFriendly}\left(n, \operatorname{primePower}\left(d, p, k, hp\right), z\right)))))$$

*Formalization.* `D5/S3/Arith/Abundancy/DefantC41Settlement.claim` (`✓ std3`).

*Citation.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

In every listed ring, for every positive rational prime and both positive exponents, the conjecture denies friendship with every nonzero element.

**Theorem 1.11 (A rational prime with a powerful friend).**

$$\neg(\forall d \in \mathbb{Z},\; (d \in K) \Rightarrow (\forall (p: \mathbb{N}) (hp: Nat.Prime\left(p\right)) (k: \mathbb{N}), (0 < k) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\forall z \in \operatorname{Nonzero}\left(d\right),\; \neg\operatorname{PowerfullyFriendly}\left(n, \operatorname{primePower}\left(d, p, k, hp\right), z\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/DefantC41Settlement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Defant (2014). *An Extension of the Abundancy Index to Certain Quadratic Rings*. DOI: [10.48550/arXiv.1506.05416](https://doi.org/10.48550/arXiv.1506.05416). URL: <https://arxiv.org/pdf/1506.05416v1#page=23>.

*Commentary.*

For d = −11 the integral basis generator π satisfies π² = π − 3. Take p = 3, k = 1, n = 2, and the challenger 7π − 3. The squared absolute values are 9 and 135. A sector element u divides an input z exactly when the norm of u divides both integral coordinates of z times the conjugate of u. The norm bound confines both divisor sets to coordinates −15 through 11 and 0 through 7. The complete divisor sets in that box give sums of 16 and 240, so both indices equal 16/9 and the absolute values differ.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.A`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.I`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.K`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.Nonzero`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.PowerfullyFriendly`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.R`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.absoluteValue`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.delta`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.primePower`
- Truth anchor: `D5/S3/Arith/Abundancy/DefantC41Settlement.result`
