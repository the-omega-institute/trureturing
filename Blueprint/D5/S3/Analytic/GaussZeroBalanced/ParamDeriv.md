# Differentiation and the parameter threshold

## Abstract

Parameter derivatives of the zero-balanced quotient

**Theorem 1.1 (The parameter quotient rule).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param_of_gauss`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param_of_gauss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the parameter derivatives of G and H and a nonzero H, the parameter derivative of f=G/H is (G_b H-G H_b)/H squared.

**Theorem 1.2 (Differentiating the Riccati identity).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.parameter_riccati_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.parameter_riccati_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, differentiating the Riccati identity in a neighborhood of b gives x K_b+(a+b+2ab x F/((a+b)(1-x)))F_b=(1-F)-a squared x F squared/((a+b) squared (1-x)). The hypotheses give the two parameter derivatives and the local Riccati identity.

**Theorem 1.3 (Parameter differentiation of Gauss series).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gauss_param`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gauss_param` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, a+s>0 and abs(x)<1, the derivative in b of gauss a b (a+b+s) x equals the sum of the parameter derivatives of its coefficients times x to the coefficient index. The coefficient is the binomial coefficient (a)_n/n! times a product of n factors (b+j)/(a+b+s+j). Each factor lies between zero and one, and its derivative lies between zero and 1/b. On a fixed parameter interval bounded away from zero, n(a)_n/(n! b) is therefore a uniform coefficient derivative bound. The unit convergence radius and polynomially weighted geometric summability justify differentiating the sum.

**Theorem 1.4 (Parameter differentiability of the contiguous quotient).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0<=x<1, the function beta maps to f a beta x is differentiable at b. The two parameter derivative series and the positive denominator discharge the quotient rule.

**Definition 1.5 (The parameter derivative series).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.gaussParam`

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.gaussParam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function gaussParam a b s x is the sum over n of the derivative at b of the nth coefficient of gauss a beta (a+beta+s), multiplied by x to the nth power.

**Theorem 1.6 (Argument differentiation of the parameter series).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gaussParam`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gaussParam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, a+s>0 and abs(x)<1, the argument derivative of gaussParam is the sum of n times its nth parameter derivative coefficient times x to the power n-1. A polynomially weighted coefficient bound supplies a summable majorant on every smaller argument interval.

**Theorem 1.7 (The mixed Gauss derivative).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gauss_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gauss_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, a+s>0 and abs(x)<1, the parameter derivative of the argument derivative of gauss equals the argument derivative of gaussParam. Both orders of differentiation give the same convergent series with nth term n times the parameter derivative of the nth coefficient times x to the power n-1.

**Theorem 1.8 (The mixed quotient derivative).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0<=x<1, both mixed derivatives of f exist and are equal. The numerator and denominator mixed Gauss derivatives pass through the quotient rule. Nonvanishing of the denominator extends to a neighborhood of the argument, including a two-sided neighborhood at zero.

**Theorem 1.9 (The parameter derivative at zero).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.deriv_f_param_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.deriv_f_param_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a and b, the parameter derivative of f at x=0 is zero because f a beta 0 is the constant one.

**Theorem 1.10 (The initial mixed derivative).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b, the argument derivative at zero of the parameter derivative of f is a times (b squared-a(a+1)) divided by the product of (a+b) squared and (a+b+1) squared. This follows from the proved mixed derivative identity and parameter differentiation of the initial slope -ab/((a+b)(a+b+1)).

**Theorem 1.11 (The parameter variational equation).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.parameter_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.parameter_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0<x<1, write h(x) for the parameter derivative of f at b, c=a+b and t=x/(1-x). Then x h prime+(c+2ab t f/c)h=(1-f)-a squared t f squared/c squared. The mixed derivative identity justifies differentiating the Riccati equation.

**Theorem 1.12 (Parameter differentiation of the original quotient).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_quot_param`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_quot_param` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b and 0<=x<1, the parameter derivative of quot equals the parameter derivative of f divided by 1-x. The contiguous identity relates the two functions throughout a parameter neighborhood.

**Theorem 1.13 (The first parameter classification).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.clause1`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.clause1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real a and b, the parameter derivative of quot is strictly negative at every x in (0,1) if and only if b<=sqrt(a(a+1)). For sufficiency, the certificate bounds (1-f)/(t f squared) strictly below ab/(c(c+1)), and the threshold puts this upper bound at most a squared/c squared. The singular endpoint comparison applied to minus h proves strict negativity. For necessity, strict negativity on (0,1) makes zero a right-side maximum of h; its initial derivative must be nonpositive, forcing b squared<=a(a+1).

## References

- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.clause1`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.deriv_f_param_zero`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.gaussParam`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_mixed`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param_of_gauss`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_f_param_zero`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gaussParam`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gauss_mixed`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_gauss_param`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.hasDerivAt_quot_param`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.parameter_equation`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/ParamDeriv.parameter_riccati_deriv`
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Comparison](Comparison.md)
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Series](Series.md)
