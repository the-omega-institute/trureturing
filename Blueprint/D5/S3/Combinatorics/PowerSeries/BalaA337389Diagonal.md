# Bala's diagonal formula for Manyama's A337389 array

## Abstract

Normalized reversion proves Bala's all-column diagonal formula for A337389.

PowerSeries has rational coefficients; X is its variable, C embeds a rational constant, constantCoeff is the constant coefficient, and coeff extracts a coefficient. The superscript -1 is the formal multiplicative inverse. Both square roots are specified by their equations and constant coefficient one.

**Definition 1.1 (The inner polynomial).**

$$\forall k: \mathbb{N}, (\operatorname{delta}\left(k\right) = 1 - (\operatorname{C}\left((2) \cdot ((k: \mathbb{Q}) + 4)\right)) \cdot (X) + ((\operatorname{C}\left((k: \mathbb{Q}) - 4\right)) \cdot (X))^{2})$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.delta` (`✓ std3`).

*Citation.* Peter Bala and Seiichi Manyama (2022). *OEIS A337389, all-column diagonal formula for Manyama's array*. URL: <https://oeis.org/A337389>.

*Commentary.*

OEIS A337389, NAME (unpaginated): Square array T(n,k), n >= 0, k >= 0, read by antidiagonals, where column k is the expansion of sqrt((1+(k-4)*x+sqrt(1-2*(k+4)*x+((k-4)*x)^2)) / (2 * (1-2*(k+4)*x+((k-4)*x)^2))). The polynomial delta k is the expression under the inner square root, with the natural parameter k cast to the rational field.

**Definition 1.2 (The normalized source column).**

$$\forall k: \mathbb{N}, (\forall d: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsColumn}\left(k, d, A\right) = ((\operatorname{constantCoeff}\left(d\right) = 1) \land (((d)^{2} = \operatorname{delta}\left(k\right)) \land ((\operatorname{constantCoeff}\left(A\right) = 1) \land ((A)^{2} = (1 + (\operatorname{C}\left((k: \mathbb{Q}) - 4\right)) \cdot (X) + d) \cdot (((2) \cdot (\operatorname{delta}\left(k\right)))^{-1}))))))))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.IsColumn` (`✓ std3`).

*Citation.* Peter Bala and Seiichi Manyama (2022). *OEIS A337389, all-column diagonal formula for Manyama's array*. URL: <https://oeis.org/A337389>.

*Commentary.*

OEIS A337389, NAME (unpaginated): Square array T(n,k), n >= 0, k >= 0, read by antidiagonals, where column k is the expansion of sqrt((1+(k-4)*x+sqrt(1-2*(k+4)*x+((k-4)*x)^2)) / (2 * (1-2*(k+4)*x+((k-4)*x)^2))). The series d is the inner root and A is the outer root. Both have constant coefficient one; multiplication by the formal inverse expresses the quotient. The entries T(n,k) are coeff n A; the array is read by antidiagonals.

**Definition 1.3 (The diagonal factor).**

$$\forall k: \mathbb{N}, (\operatorname{phi}\left(k\right) = ((1 + (\operatorname{C}\left((k: \mathbb{Q}) - 2\right)) \cdot (X) + (X)^{2}) \cdot ((1 + X)^{2})) \cdot (((1 - X)^{2})^{-1}))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.phi` (`✓ std3`).

*Citation.* Peter Bala and Seiichi Manyama (2022). *OEIS A337389, all-column diagonal formula for Manyama's array*. URL: <https://oeis.org/A337389>.

*Commentary.*

OEIS A337389, final FORMULA (unpaginated): Conjecture: the k-th column entries, k >= 0, are given by [x^n] ( (1 + (k-2)*x + x^2)*(1 + x)^2/(1 - x)^2 )^n. This is true for k = 0 and k = 4. - _Peter Bala_, May 03 2022 The denominator (1-X)^2 is a unit and the expansion is at zero.

**Definition 1.4 (The all-column conjecture).**

$$claim = (\forall k: \mathbb{N}, ((\exists d: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsColumn}\left(k, d, A\right)))) \land (\forall d: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsColumn}\left(k, d, A\right)) \implies (\forall n: \mathbb{N}, (\operatorname{coeff}\left(n, A\right) = \operatorname{coeff}\left(n, (\operatorname{phi}\left(k\right))^{n}\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.claim` (`✓ std3`).

*Citation.* Peter Bala and Seiichi Manyama (2022). *OEIS A337389, all-column diagonal formula for Manyama's array*. URL: <https://oeis.org/A337389>.

*Commentary.*

OEIS A337389, final FORMULA (unpaginated): Conjecture: the k-th column entries, k >= 0, are given by [x^n] ( (1 + (k-2)*x + x^2)*(1 + x)^2/(1 - x)^2 )^n. This is true for k = 0 and k = 4. - _Peter Bala_, May 03 2022 The natural indices include n=0 and every k>=0. Existence of the normalized pair is included, and the identity is asserted for every normalized pair.

**Theorem 1.5 (The all-column diagonal identity).**

$$\forall k: \mathbb{N}, ((\exists d: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsColumn}\left(k, d, A\right)))) \land (\forall d: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsColumn}\left(k, d, A\right)) \implies (\forall n: \mathbb{N}, (\operatorname{coeff}\left(n, A\right) = \operatorname{coeff}\left(n, (\operatorname{phi}\left(k\right))^{n}\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala and Seiichi Manyama (2022). *OEIS A337389, all-column diagonal formula for Manyama's array*. URL: <https://oeis.org/A337389>.

*Commentary.*

Invert X/phi k compositionally to obtain w=X*phi k(w), and put v=(phi k)^(-1)(w), Y=X*w+v and A=PowerSeries.derivative w*v. Eliminating w gives Y^2+(C(k)*X-1)*Y+2*(C(k)-2)*X^2+2*X=0. Its discriminant gives d=2*Y+C(k)*X-1 with d^2=delta k. Differentiating the quadratic and cancelling the units Y-2X and Y+2X gives the outer square equation. Lagrange inversion gives coeff n A=coeff n ((phi k)^n). Normalized square-root uniqueness identifies every source pair with this pair. The argument includes k=0 and k=4 without dividing by k or k-4.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.IsColumn`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.claim`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.delta`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.phi`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA337389Diagonal.result`
- Dependency: [D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix](../HannaLambertW/OeisA386655LambertWEgfModSix.md)
