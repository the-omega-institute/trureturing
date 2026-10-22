# Coefficient and derivative bounds

## Abstract

Normalized elliptic tails

**Definition 1.1 (Normalized tail coefficients).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.b`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Bounds.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive k, b(k,a) is (1-a/k)/(k(k+1)) times the product of 1-a^2/j^2 over 1<=j<k. The index zero is not used in the tail.

**Theorem 1.2 (Positive summable majorants).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.b_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.b_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural k and 0<=a<=3/4, the coefficient b(k,a) is strictly positive and at most 1/(k(k+1)). Every factor of the finite product lies in (0,1].

**Theorem 1.3 (Coefficients at zero).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.b_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.b_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a=0 the normalized coefficient equals 1/(k(k+1)). This identity supplies the exact tail value at zero.

**Theorem 1.4 (Strictly negative coefficient derivatives).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_b_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_b_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive k and 0<=a<=3/4, the derivative of b(k,a) is strictly negative and has absolute value at most 4/(k(k+1)). Differentiating the product leaves nonpositive contributions. The finite reciprocal-square sum is at most two, and the derivative of the leading linear factor is strictly negative.

**Definition 1.5 (Normalized infinite tails).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.U`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Bounds.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U(n,a) is the sum of b(k+n+1,a) over natural k. The rational coefficient majorant is summable for each fixed n.

**Theorem 1.6 (Termwise differentiation).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.hasDerivAt_U`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.hasDerivAt_U` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and 0<a<3/4, U(n,a) has derivative equal to the sum of the derivatives of its coefficient functions. The uniform summable derivative majorant and convergence at a=1/2 justify differentiation on the preconnected open interval (0,3/4).

**Theorem 1.7 (Strict positivity of the tail).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.U_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.U_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and 0<=a<=3/4, U(n,a)>0. The series converges and every summand is positive.

**Theorem 1.8 (Strict decrease of the normalized tail).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_U_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_U_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and 0<a<3/4, the derivative of U(n,a) is strictly negative. Termwise differentiation gives a convergent series of negative derivatives.

**Theorem 1.9 (Continuity through parameter zero).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.continuousOn_U`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.continuousOn_U` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized tail is continuous on [0,3/4]. Summable bounds for the continuous coefficient polynomials give uniform convergence, including at zero.

**Theorem 1.10 (Exact tail value at zero).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.U_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.U_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, U(n,0)=1/(n+1). The rational summands at zero telescope as 1/k-1/(k+1).

**Theorem 1.11 (A uniform tail derivative bound).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Bounds.norm_deriv_U_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EllipticTailExponent/Bounds.norm_deriv_U_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<a<3/4, the norm of the derivative of U(n,a) is at most four times the sum of 1/((k+n+1)(k+n+2)). This parameter-independent finite bound makes a times the derivative tend to zero as a decreases to zero.

## References

- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.U`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.U_pos`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.U_zero`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.b`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.b_bounds`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.b_zero`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.continuousOn_U`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_U_neg`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.deriv_b_bounds`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.hasDerivAt_U`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Bounds.norm_deriv_U_le`
- Dependency: [D5/S3/Analytic/EllipticTailExponent/Defs](Defs.md)
