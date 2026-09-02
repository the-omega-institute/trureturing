# Jensen Polynomial Obstruction

## Abstract

The Jensen polynomial tower turns failure of a real-zero criterion into a negative coefficient or one finite nonhyperbolic witness.

**Definition 1.1 (Shifted Jensen polynomial).**

Lean statement: `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.jensenPolynomial`

*Formalization.* `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.jensenPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For degree d and shift n, the polynomial sums choose(d,k) times gamma(n+k) times X^k over k from zero through d.

**Definition 1.2 (Polynomial hyperbolicity).**

Lean statement: `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.PolynomialHyperbolic`

*Formalization.* `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.PolynomialHyperbolic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real polynomial is hyperbolic when every root after mapping its coefficients to the complex numbers has zero imaginary part.

**Theorem 1.3 (Failure has a negative coefficient or a nonhyperbolic Jensen witness).**

$$\begin{aligned}\forall a, \gamma: \mathbb{N} \to \mathbb{R}, RH: \operatorname{Prop},\\(\forall m\in\mathbb{N}, \gamma\left(m\right) = m! a\left(m\right)) \land (RH \Rightarrow (\forall d, n\in\mathbb{N}, \operatorname{Hyperbolic}\left(\operatorname{J}\left(\gamma, d, n\right)\right))) \land ((\forall m\in\mathbb{N}, 0 \leq a\left(m\right)) \land (\forall d, n\in\mathbb{N}, \operatorname{Hyperbolic}\left(\operatorname{J}\left(\gamma, d, n\right)\right)) \Rightarrow RH) \Rightarrow\\(RH \Rightarrow (\forall d, n\in\mathbb{N}, \operatorname{Hyperbolic}\left(\operatorname{J}\left(\gamma, d, n\right)\right))) \land\\(\neg RH \Rightarrow (\exists m\in\mathbb{N}, a\left(m\right) < 0) \lor (\exists d, n\in\mathbb{N}, \neg \operatorname{Hyperbolic}\left(\operatorname{J}\left(\gamma, d, n\right)\right))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.jensen_polynomial_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential-series coefficients satisfy gamma(m)=m!a(m). The two supplied Jensen-Polya bridges say that RH makes every shifted Jensen polynomial hyperbolic, while nonnegative coefficients and a fully hyperbolic tower imply RH.

If RH fails and no coefficient is negative, every coefficient is nonnegative. If no finite nonhyperbolic witness existed either, the reverse bridge would imply RH, a contradiction.

The polynomial and hyperbolicity predicate are concrete Lean definitions. The deep Laguerre-Polya implications remain explicit hypotheses because neither this repository nor pinned Mathlib contains that analytic classification theorem.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.PolynomialHyperbolic`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.jensenPolynomial`
- Truth anchor: `D5/S3/Zeros/Jensen/JensenPolynomialObstruction.jensen_polynomial_obstruction`
