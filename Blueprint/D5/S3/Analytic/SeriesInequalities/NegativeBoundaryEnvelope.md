# Negative Boundary Envelope

## Abstract

Negative real boundaries share the envelope attained by the constant negative source.

**Theorem 1.1 (An attained envelope for the nonlinear recurrence).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/NegativeBoundaryEnvelope.negative_boundary_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/NegativeBoundaryEnvelope.negative_boundary_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a real-like field, including the real and complex numbers. Assume A>0, 0<rho<1 and A rho=(1-rho)^2. The scalar amplitude is defined by u(0)=A and u(k+1)=u(k)+A sum over j=0,...,k of u(j). The actual extension has E(a)(n,0)=a(n) and E(a)(n,k+1)=E(a)(n+1,k)-sum over j=0,...,k of E(a)(n,j)a(k-j).

For every natural k, u(k) is nonnegative and rho^k u(k)=A/(1+rho) times (1+rho^(2k+1)). For every pair n,k, the actual constant-negative output is E(-A)(n,k)=-u(k), where real scalars are embedded in K.

For every real sequence x satisfying 0<=x(n)<=A at every natural n, and every pair n,k, there exists a real q with 0<=q<=u(k) and E(-x)(n,k)=-q in K. This includes the zeroth row and every column. In particular it applies to each actual negative source truncation.

Strong induction through the same subtraction and convolution recurrence proves the comparison: changing the signs converts each product to a nonnegative contribution. The constant source attains the common upper envelope. Subtracting successive scalar recurrences gives u(k+2)=(A+2)u(k+1)-u(k); its two initial values and the critical identity establish the displayed formula by two-step induction.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/NegativeBoundaryEnvelope.negative_boundary_envelope`
- Dependency: [D5/S3/Analytic/SeriesInequalities/FiniteSourceClosure](FiniteSourceClosure.md)
