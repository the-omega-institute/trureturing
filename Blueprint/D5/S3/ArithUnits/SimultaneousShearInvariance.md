# Simultaneous Shear Invariance

## Abstract

Two independent simultaneous translations eliminate both polynomial variables.

**Theorem 1.1 (Independence of two translated variables).**

Lean statement: `D5/S3/ArithUnits/SimultaneousShearInvariance.eq_constant_of_two_shears`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/SimultaneousShearInvariance.eq_constant_of_two_shears` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a commutative integral domain of characteristic zero, sigma any set of coefficient variables, and iota an injection from the four-element index set into sigma. In the polynomial ring A over R on sigma, write a, b, r, s for the generators indexed by iota(0), iota(1), iota(2), iota(3). Let F be a polynomial in d and u over A. If the translations (d,u) to (d+a,u+r) and (d,u) to (d+b,u+s) each fix F, then F equals its constant coefficient with respect to d and u. There is no restriction on degree or homogeneity, and zero and constant polynomials are included.

For any base point x and direction v, evaluate F along x + Tv, obtaining a univariate polynomial in T. Translation invariance makes its values at all nonnegative integers equal to its value at zero. Characteristic zero supplies infinitely many distinct such parameters, and the integral domain root bound makes the line polynomial constant. Thus invariance holds for every parameter in the coefficient domain, including negative parameters.

The general domain argument uses translation vectors v and w with nonzero determinant delta. For arbitrary d and u in that domain, take alpha = w(1)d - w(0)u and beta = v(0)u - v(1)d. Then alpha v + beta w = (delta d, delta u). Applying the two line invariances shows F has its value at zero on every such pair. Multiplication by the nonzero delta is injective, so its range is infinite. Multivariate polynomial extensionality on the product of these two infinite ranges proves the identity. This argument requires no division by the determinant.

For simultaneous color transport, take the base domain to be the rationals and A the polynomial ring in a, b, c, r, s, t and any auxiliary variables. The two distinguished variables are d and u; use v = (a,r) and w = (b,s). The determinant as - br is a nonzero element of A: evaluation at a = s = 1 and b = r = 0 sends it to 1. This evaluation proves a polynomial is nonzero; it does not assert nonvanishing at every point. The conclusion makes both formal partial derivatives zero, hence also gives a partial_d F + r partial_u F = 0 and b partial_d F + s partial_u F = 0. Dependence of F on any auxiliary variable and degree zero in either color are retained.

The statement concerns polynomial translation invariants. Applying it to graph coefficient tensors requires the coefficient identification and the derivation of those translations from the actual antisymmetry, IHX, and commuting-leg relations.

## References

- Truth anchor: `D5/S3/ArithUnits/SimultaneousShearInvariance.eq_constant_of_two_shears`
