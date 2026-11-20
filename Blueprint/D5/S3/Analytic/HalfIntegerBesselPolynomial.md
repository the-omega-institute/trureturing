# Half-integer Bessel polynomial and its reflected Wronskian

## Abstract

The normalized half-integer Bessel polynomial and its reflection give an exact Wronskian.

**Definition 1.1 (Normalized factorial coefficient).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselPolynomial.coefficient`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselPolynomial.coefficient` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For natural m and k with k at most m, the rational coefficient a(m,k) is (m+k)! divided by 2^k k! (m-k)!. For k greater than m it is zero.

**Definition 1.2 (Finite carrier polynomial).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselPolynomial.carrier`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselPolynomial.carrier` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For each natural m the rational polynomial P is the sum of a(m,k) X^k for k from zero through m. Its indeterminate corresponds to the reciprocal argument of the finite half-integer Bessel carrier.

**Theorem 1.3 (Coefficient recurrence).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselPolynomial.coefficient_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselPolynomial.coefficient_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For every natural m and k, 2(k+1) a(m,k+1) equals (m-k)(m+k+1) a(m,k), with the factors taken in the rationals. The identity includes k=m and all indices above the degree.

**Theorem 1.4 (Differential equation in the reciprocal argument).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselPolynomial.carrier_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselPolynomial.carrier_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, its carrier P satisfies the rational polynomial identity X^2 P'' + (2X+2) P' = m(m+1) P. Each coefficient of this identity reduces to the factorial recurrence.

**Theorem 1.5 (Reflected polynomial Wronskian).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselPolynomial.reflected_wronskian`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselPolynomial.reflected_wronskian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, let P be its carrier and Q(X) = P(-X). Then 2 P Q - X^2 (P Q' - P' Q) = 2 in the rational polynomial ring. The two differential equations make the derivative vanish. Since P(0) = Q(0) = 1, the constant is 2.

## References

- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselPolynomial.carrier`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselPolynomial.carrier_ode`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselPolynomial.coefficient`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselPolynomial.coefficient_succ`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselPolynomial.reflected_wronskian`
