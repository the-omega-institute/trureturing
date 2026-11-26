# Chamber expansion and the removable diagonal

## Abstract

Ordinary coefficients of the regular half-current correction

In Bakalov–Kac v1, §4.2, equation (4.23), the fractional bracket pairs a positive mode r=n+1/2 with the negative mode -r and gives r times the Gram entry. Removing the Gram entry and the half-density factor (u*v)^(-1/2) from the current contraction gives u^(-1) times the sum of (n+1/2)*(v/u)^n in the v-inner chamber. With x=v/u, Mathlib’s invOneSubPow at power two gives (1+x)/(2*(1-x)^2), whose coefficient of x^n is n+1/2. The Lean coefficient and denominator identities thus give the free kernel (u+v)/(2*(u-v)^2).

**Definition 1.1 (Regular Cauchy correction series).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the native coordinate F(u)=lambda*u/(1-eta*u), the normalized roots b and c of 1-eta*u and 1-eta*v have constant term one. The weight-one pullback of the current after extracting the half-density factor has multiplier F'(u)*sqrt(u/F(u)) = root/b^3, where root^2=lambda fixes the lift. The regular chamber expression is eta*(1+b*c)/(2*b*c*(b+c)^2). The second variable is expanded first with Laurent coefficients in the first variable.

**Theorem 1.2 (Every ordinary bivariate coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the dressed and undressed chamber expansions by (u-v)^2 clears their denominators. The square-root relations then identify their difference with the regular expression. For a fixed inner coefficient q, substitution uses only powers zero through q. Nonnegative outer coefficients of the original chamber kernel vanish, so the contraction sum gives the ordinary coefficient of the regular difference.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport](OriginalHalfCurrentTransport.md)
