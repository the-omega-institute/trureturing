# Chamber expansion and the removable diagonal

## Abstract

Ordinary coefficients of the regular half-current correction

**Definition 1.1 (Regular Cauchy correction series).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The normalized roots b and c of 1-eta*u and 1-eta*v have constant term one. The regular chamber expression is eta*(1+b*c)/(2*b*c*(b+c)^2). The second variable is expanded first with Laurent coefficients in the first variable.

**Theorem 1.2 (Every ordinary bivariate coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Multiplying the dressed and undressed chamber expansions by (u-v)^2 clears their denominators. The square-root relations then identify their difference with the regular expression. For a fixed inner coefficient q, substitution uses only powers zero through q. Nonnegative outer coefficients of the original chamber kernel vanish, so the contraction sum gives the ordinary coefficient of the regular difference.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regularSeries`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy.regular_series_coefficient`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport](OriginalHalfCurrentTransport.md)
