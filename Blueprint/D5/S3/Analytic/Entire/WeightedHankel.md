# Removing the quadratic weight by scalar differentiation

## Abstract

Removing the quadratic weight by scalar differentiation.

**Theorem 1.1 (Removing the quadratic weight by scalar differentiation).**

Lean statement: `D5/S3/Analytic/Entire/WeightedHankel.finite_translation_space_of_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/WeightedHankel.finite_translation_space_of_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every entire complex f, finite entire separation of (z-w)^2*f(z+w) implies finite dimension of the complete span of its complex translates. The proof never divides by the quadratic factor on its zero diagonal.

The operator partial_z minus partial_w annihilates the dependence on z+w. Applying it twice to the weighted kernel gives exactly 8*f(z+w). Differentiating a finite separated sum preserves finite separation, so the unweighted Hankel kernel is finitely separated and the translation-span result applies.

The product-rule calculation takes place on scalar entire functions. It is an intermediate part of the complete finite-separation iff exponential-polynomial theorem. It supplies no spectral, entropy or physical realization assumption.

## References

- Truth anchor: `D5/S3/Analytic/Entire/WeightedHankel.finite_translation_space_of_weighted`
- Dependency: [D5/S3/Analytic/Entire/SeparatedKernel](SeparatedKernel.md)
