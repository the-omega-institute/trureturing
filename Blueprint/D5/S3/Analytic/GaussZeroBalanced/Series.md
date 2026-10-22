# Series identities

## Abstract

Positive Gauss series and the Riccati equation

**Theorem 1.1 (Lower bound by the constant term).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.one_le_gauss`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.one_le_gauss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real a, b and c and 0 <= x < 1, gauss a b c x is at least one. All coefficients and all terms are nonnegative, and the constant term is one.

**Theorem 1.2 (Positivity).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.gauss_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.gauss_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real a, b and c and 0 <= x < 1, gauss a b c x is strictly positive.

**Theorem 1.3 (Differentiation in the argument).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_gauss`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_gauss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real a, b and c and 0 <= x < 1, the derivative of gauss a b c at x is (a*b/c) times gauss (a+1) (b+1) (c+1) x. At zero this is a two-sided derivative. A radius strictly between abs(x) and one supplies a summable majorant for the termwise derivatives.

**Theorem 1.4 (The denominator-parameter shift).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.contiguous_G`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.contiguous_G` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 <= x < 1, put c=a+b, H(x)=gauss a b c x, and G(x)=gauss a b (c+1) x. Then x times the derivative of G is c(H-G). The coefficient relation is (c+n)G[n]=cH[n].

**Theorem 1.5 (The zero-balanced derivative identity).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.contiguous_H`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.contiguous_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 <= x < 1, put c=a+b, H(x)=gauss a b c x, and G(x)=gauss a b (c+1) x. Then (1-x) times the derivative of H is (ab/c)G. The coefficient recurrence cancels the remaining terms because c=a+b.

**Theorem 1.6 (The origin value).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.f_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.f_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a and b, f a b 0 equals one.

**Theorem 1.7 (The positive contiguous quotient).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.f_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.f_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 <= x < 1, f a b x is positive.

**Theorem 1.8 (The strict upper bound).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.f_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.f_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 < x < 1, f a b x is less than one. The first contiguous identity and the positive derivative of G give G(x)<H(x).

**Theorem 1.9 (The quotient derivative).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_f`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 <= x < 1, with c=a+b, H(x)=gauss a b c x and G(x)=gauss a b (c+1) x, the function f a b has derivative (deriv(G,x)H(x)-G(x)deriv(H,x))/H(x)^2 at x. Positivity of H justifies the quotient rule, including at zero.

**Theorem 1.10 (Continuity including the origin).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.continuousOn_f`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.continuousOn_f` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, f a b is continuous on the half-closed interval [0,1).

**Theorem 1.11 (The relation between the quotients).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.quot_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.quot_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 <= x < 1, quot a b x equals f a b x divided by 1-x. The derivative identity cancels the positive factor ab/(a+b).

**Theorem 1.12 (The Riccati equation).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.riccati`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.riccati` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0 < x < 1, put c=a+b. The function f satisfies x deriv(f,x)=c(1-f(x))-(ab/c)(x/(1-x))f(x)^2. Both contiguous identities enter the quotient rule; positivity of the denominator permits the algebraic cancellations.

**Theorem 1.13 (The initial slope).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Series.deriv_f_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Series.deriv_f_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, the derivative of f a b at zero is -ab/((a+b)(a+b+1)). This follows by evaluating the quotient rule at the series origin.

## References

- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.contiguous_G`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.contiguous_H`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.continuousOn_f`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.deriv_f_zero`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.f_lt_one`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.f_pos`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.f_zero`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.gauss_pos`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_f`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_gauss`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.one_le_gauss`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.quot_eq`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Series.riccati`
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Defs](Defs.md)
