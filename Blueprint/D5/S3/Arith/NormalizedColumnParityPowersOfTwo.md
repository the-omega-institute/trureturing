# A144637 Normalized Column Parity

## Abstract

The zero-constant-coefficient solution of the cubic equation recorded for A144637 is integral and odd exactly at positive powers of two.

The series treated here is the unique power series with zero constant coefficient satisfying 36y^3+3y^2+(1+6x)y=x^2. OEIS A144637 records that its exponential generating function A satisfies this equation through y=(1/18)A(6x), so that coefficient n of y would equal 6^n a(n)/(18 n!). That identification is quoted from the entry and is not proved below; every statement below concerns only the series defined by the equation.

**Definition 1.1 (The normalized integral series).**

$$normalizedColumnSeries: \operatorname{PowerSeries}\left(\mathbb{Z}\right), normalizedColumnSeries = \operatorname{mk}\left(normalizedCoeff\right)$$

*Formalization.* `D5/S3/Arith/NormalizedColumnParityPowersOfTwo.normalizedColumnSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer series y is built by a finite-prefix recursion. At degree n, the coefficients of the square and cube depend only on degrees below n because the constant coefficient is zero. The coefficient of y in 1+6x is one, so the degree-n equation determines the next integer coefficient without division. This construction records integrality in the coefficient type itself.

**Theorem 1.2 (Odd coefficients occur exactly at positive powers of two).**

$$(\operatorname{constantCoeff}\left(normalizedColumnSeries\right) = 0) \land ((36 \cdot normalizedColumnSeries^{3} + 3 \cdot normalizedColumnSeries^{2} + \left(1 + 6 \cdot X\right) \cdot normalizedColumnSeries = X^{2}) \land (((\forall z: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(z\right) = 0) \Rightarrow (36 \cdot z^{3} + 3 \cdot z^{2} + \left(1 + 6 \cdot X\right) \cdot z = X^{2}) \Rightarrow z = normalizedColumnSeries)) \land (\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{coeff}\left(n, normalizedColumnSeries\right)\right) \iff \exists k: \mathbb{N}, (1 \le k) \land (n = 2^{k}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NormalizedColumnParityPowersOfTwo.a144637_normalized_column_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem proves at once that y has constant coefficient zero, satisfies the complete cubic equation, and is the unique integer power-series solution with that constant coefficient. It then states the parity equivalence for every natural index, including the zero and one boundary cases.

Reducing the cubic equation modulo two removes the terms multiplied by 36 and 6 and changes the coefficient 3 to one. The result is y^2+y=x^2. The general characteristic-two uniqueness theorem identifies this zero-constant root with x^2+x^4+x^8+.... The Frobenius square doubles every exponent, so its support consists exactly of 2^k for k at least one. Reduction of an integer to one modulo two is equivalent to oddness, giving both directions. This is a symbolic proof with no bounded enumeration or checker.

## References

- Truth anchor: `D5/S3/Arith/NormalizedColumnParityPowersOfTwo.a144637_normalized_column_parity`
- Truth anchor: `D5/S3/Arith/NormalizedColumnParityPowersOfTwo.normalizedColumnSeries`
- Dependency: [D5/S3/Arith/ArtinSchreierQuadraticRootUniqueness](ArtinSchreierQuadraticRootUniqueness.md)
- Dependency: [D5/S3/Arith/ArtinSchreierTracePowersOfTwo](ArtinSchreierTracePowersOfTwo.md)
