# Polynomial Reflection and Numerator Reciprocity

## Abstract

Polynomial reflection gives exact-degree palindromic generating-series numerators.

**Theorem 1.1 (Reflection gives a palindromic numerator).**

Lean statement: `D5/S3/Analytic/PolynomialReflectionNumerator.palindromic_numerator_of_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PolynomialReflectionNumerator.palindromic_numerator_of_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real polynomial p of degree at most n, normalized by p(0)=1 and satisfying p(-1-x)=(-1)^n p(x), has a generating-series numerator of degree exactly n over (1-z)^(n+1). Its coefficients at j and n-j coincide. Expansion in the binomial polynomial basis converts reflection of p into coefficient reversal of the numerator.

## References

- Truth anchor: `D5/S3/Analytic/PolynomialReflectionNumerator.palindromic_numerator_of_reflection`
