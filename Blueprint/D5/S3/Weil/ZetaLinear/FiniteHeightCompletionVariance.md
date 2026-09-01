# Finite-Height Completion Variance

## Abstract

Finite-height completion variance is a finite multiplicity-weighted sum of squared critical-line displacements and is nonnegative term by term.

**Definition 1.1 (The finite-height completion variance is nonnegative).**

Lean statement: `D5/S3/Weil/ZetaLinear/FiniteHeightCompletionVariance.finite_height_completion_variance_nonnegative`

*Formalization.* `D5/S3/Weil/ZetaLinear/FiniteHeightCompletionVariance.finite_height_completion_variance_nonnegative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The completion function xi and the natural-number multiplicity are abstract parameters. A finite zero window records T positive, a finite set of complex points, and exact membership by xi(rho) equal to zero with ordinate in (0,T]. This explicit premise supplies the finiteness not proved in the source atom.

Each summand is the multiplicity times the square of the canonical critical displacement Re(rho)-1/2, so it is nonnegative. The formal theorem states both termwise nonnegativity on the window and nonnegativity of the resulting finite sum.

The definition is nonempty and nondegenerate: xi(rho)=rho-i, T=1, the singleton window {i}, and multiplicity one realize variance 1/4, which is strictly positive.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/FiniteHeightCompletionVariance.finite_height_completion_variance_nonnegative`
- Dependency: [D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening](ReflectedZeroModePhaseFlattening.md)
