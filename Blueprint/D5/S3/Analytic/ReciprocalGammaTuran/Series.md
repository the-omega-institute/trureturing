# The entire series and its coefficients

## Abstract

Convergent reciprocal Gamma series and boundary Turanian recurrences.

**Definition 1.1 (The reciprocal Gamma series).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.F`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real b and x, F(b,x) is the sum over natural n of rgamma(n+b) times x to the power n.

**Definition 1.2 (Formal coefficient sequences).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.formalSeries`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.formalSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real sequence g and real b, formalSeries(g,b) has coefficient g(n)rgamma(n+b) in every natural degree n.

**Definition 1.3 (The boundary Turanian).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundarySeries`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real t, the formal boundary series is formalSeries(1,0) squared minus formalSeries(1,-t) times formalSeries(1,t).

**Definition 1.4 (Boundary coefficients).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.d`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t and natural m, d(t,m) is the degree m coefficient of the formal boundary series.

**Theorem 1.5 (Infinite convergence radius).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.entire_series`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.entire_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real b, F(b,.) has the scalar power series with coefficients rgamma(n+b) around zero on the ball of infinite radius. The norm bounds hold at every nonnegative radius.

**Theorem 1.6 (Convergence at every argument).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasSum_series`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasSum_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real b and x, the defining series sums to F(b,x). The terms are absolutely summable: beyond the finitely many nonpositive Gamma arguments, the ratio is x divided by n+b and tends to zero.

**Theorem 1.7 (Exact formal Cauchy coefficients).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.coeff_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.coeff_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence g, real mu, alpha and beta, and natural m, the coefficient of formalSeries(g,mu+alpha)formalSeries(g,mu+beta) minus formalSeries(g,mu)formalSeries(g,mu+alpha+beta) equals turanCoeff(g,mu,alpha,beta,m). The finite summation bounds justify replacing the natural difference m-k by its real value.

**Theorem 1.8 (Boundary specialization).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.turanCoeff_one_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.turanCoeff_one_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t and natural m, turanCoeff(1,-t,t,t,m) equals d(t,m).

**Theorem 1.9 (Coefficients of the actual products).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasSum_turanCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasSum_turanCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real mu, alpha, beta and x, the series with terms turanCoeff(1,mu,alpha,beta,m)x to the power m sums to F(mu+alpha,x)F(mu+beta,x) minus F(mu,x)F(mu+alpha+beta,x). Absolute convergence of each factor permits the Cauchy product and subtraction, identifying the finite formula with the ordinary power series coefficient.

**Theorem 1.10 (The zero parameter exponential).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.F_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.F_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x, F(0,x) equals x times exp(x). The Gamma values at positive integers give the factorial coefficients, and the value at zero vanishes.

**Theorem 1.11 (Termwise differentiation).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasDerivAt_F`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasDerivAt_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real b and x, F(b,.) has derivative F(b,x)+(1-b)F(b+1,x) at x. The differentiated series has a summable bound on every bounded interval.

**Theorem 1.12 (The differential equation).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.differential_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.differential_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real b and x, x times the derivative of F(b,.) at x equals (x+1-b)F(b,x)+(b-1)rgamma(b). This formula also holds at x=0 and at every parameter pole.

**Theorem 1.13 (The formal differential equation).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.formal_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.formal_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real b and f=formalSeries(1,b), X times the formal derivative of f equals (X+1-b)f plus the constant (b-1)rgamma(b). The identity includes poles and follows coefficient by coefficient from the Gamma recurrence.

**Definition 1.14 (The forcing coefficients).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.r`

*Formalization.* `D5/S3/Analytic/ReciprocalGammaTuran/Series.r` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t and natural m, r(t,m) equals (t+1)rgamma(-t)rgamma(m+t) plus (1-t)rgamma(t)rgamma(m-t).

**Theorem 1.15 (The boundary differential equation).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundary_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundary_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real t and the formal boundary series D, X times its derivative is 2(X+1)D plus (t+1)rgamma(-t)formalSeries(1,t) plus (1-t)rgamma(t)formalSeries(1,-t). Applying the Leibniz rule to the two products gives this identity.

**Theorem 1.16 (The boundary coefficient recurrence).**

Lean statement: `D5/S3/Analytic/ReciprocalGammaTuran/Series.coefficient_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReciprocalGammaTuran/Series.coefficient_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t and natural m at least three, (m-2)d(t,m) equals 2d(t,m-1)+r(t,m). This is the degree m coefficient of the formal differential equation.

## References

- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.F`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.F_zero`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundarySeries`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.boundary_recurrence`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.coeff_mul`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.coefficient_recurrence`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.d`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.differential_recurrence`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.entire_series`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.formalSeries`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.formal_recurrence`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasDerivAt_F`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasSum_series`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.hasSum_turanCoeff`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.r`
- Truth anchor: `D5/S3/Analytic/ReciprocalGammaTuran/Series.turanCoeff_one_boundary`
- Dependency: [D5/S3/Analytic/ReciprocalGammaTuran/Defs](Defs.md)
