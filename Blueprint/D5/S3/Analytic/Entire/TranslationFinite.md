# Differentiation preserves finite translation spaces

## Abstract

Differentiation preserves finite translation spaces.

**Theorem 1.1 (Differentiation preserves finite translation spaces).**

Lean statement: `D5/S3/Analytic/Entire/TranslationFinite.deriv_mem_of_finite_translation_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/TranslationFinite.deriv_mem_of_finite_translation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite-dimensional complex submodule W of all functions Complex -> Complex, if translation by every complex number preserves W, then the scalar derivative of each entire member of W also lies in W. The topology is pointwise convergence on the whole complex plane. No completed Fock differentiation operator or boundedness of differentiation in the Fock norm is assumed.

For each nonzero t, t inverse times (f(.+t)-f) is an actual member of W. The entire derivative is its pointwise limit as t tends to zero through nonzero complex values. The finite-dimensional submodule is closed in the Hausdorff product topology, so the limit belongs to W. This constructs derivativeEnd from actual scalar derivatives; it is consumed by the generalized-eigenspace classification.

The complete translation span contains the original function, is invariant under every complex translation, and consists of entire functions when the generator is entire. These are the inputs to the direct holomorphic proof of the classical finite-translation-space mechanism. The source-specific pointwise realization and its analytic joins are repository-derived; no a.e. measurable-function theorem is substituted for an everywhere entire statement.

## References

- Truth anchor: `D5/S3/Analytic/Entire/TranslationFinite.deriv_mem_of_finite_translation_invariant`
