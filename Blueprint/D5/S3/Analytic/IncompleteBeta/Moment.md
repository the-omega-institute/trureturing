# Moment kernel

## Abstract

Finite convolution and beta moment kernel for incomplete beta coefficients.

**Definition 1.1 (Finite coefficient convolution).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.convolution`

*Formalization.* `D5/S3/Analytic/IncompleteBeta/Moment.convolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The convolution sums products of the Gamma coefficients at complementary indices.

**Definition 1.2 (Symmetric beta kernel).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.W`

*Formalization.* `D5/S3/Analytic/IncompleteBeta/Moment.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite kernel is the sum of products of the two powered factors, divided by the corresponding Gamma factors.

**Theorem 1.3 (Beta moment representation).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.convolution_eq_betaMean`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Moment.convolution_eq_betaMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, s and t, the finite coefficient convolution is Gamma(2a+s+t+n) divided by Gamma(s)Gamma(t), times the integral from zero to one of u^(s-1)(1-u)^(t-1)W(u). Dividing the integral by the beta normalizer gives the normalized beta mean with a common factor depending only on s+t.

**Theorem 1.4 (Continuity of the kernel).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.W_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Moment.W_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and every natural n, the finite kernel is continuous on the closed unit interval, since all its power exponents are positive.

**Theorem 1.5 (Reflection symmetry).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.W_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Moment.W_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection about one half leaves W unchanged; reversal of the finite summation interchanges the two powers and their Gamma factors.

**Theorem 1.6 (Telescoping derivative).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.W_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Moment.W_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open unit interval, the derivative of W is u^(a-1)(1-u)^(a+n)/(Gamma(a)Gamma(a+n+1)) minus u^(a+n)(1-u)^(a-1)/(Gamma(a+n+1)Gamma(a)). The product rule and the Gamma recurrence give adjacent terms whose finite sum telescopes.

**Theorem 1.7 (Strict increase toward the midpoint).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Moment.W_strictMonoOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Moment.W_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, W is strictly increasing on the closed interval from zero to one half. Its derivative is strictly positive in the interior; continuity supplies the endpoints.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.W`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.W_continuousOn`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.W_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.W_strictMonoOn`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.W_symm`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.convolution`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Moment.convolution_eq_betaMean`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
