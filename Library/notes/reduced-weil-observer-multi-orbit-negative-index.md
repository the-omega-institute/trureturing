# Reduced Weil observer and multi-orbit negative index

## Purpose

This note records the mathematical and formalization provenance for the four-node observer layer added to PR #5065.

## Library-first inputs

The implementation reuses the following repository owners:

- `D5/S3/Weil/TestFunctions/EvenTestFunctionFiniteInterpolation.even_weilTestFunction_finite_interpolation` for exact finite interpolation by even compactly supported smooth tests.
- `D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.fourierLaplace_convolutionSquare_complex` for complex-frequency convolution-square factorization.
- `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition` for the one-orbit even-minus-odd identity.
- `D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable.symmetricConvergent_of_zeroData` for unconditional symmetric zero-sum convergence.
- `RHLinalg.negIndex`, `RHLinalg.posIndex`, and `FiniteSpectralLocalizer.posIndex_neg_eq_negIndex` for spectral inertia.
- The canonical `ZeroData`, mirror, multiplicity, and Fourier-Laplace interfaces already present in the repository and in the earlier layers of PR #5065.

No second zero predicate, second multiplicity function, parallel negative-index definition, or full-rank observer axiom is introduced.

## Observer correction

For scalar even Weil tests, the finite evaluation

\[
E_T(g)(n,k)=\widehat g(\gamma_n)
\]

is constant in the analytic-multiplicity copy `k`. It is also invariant under functional-equation reflection because `gamma(reflection n) = -gamma(n)` and the transform of an even test is even.

Therefore the ambient multiplicity-expanded mirror-odd space is generally larger than the scalar observer's reachable space. The new formalization computes inertia on a reduced observer space and proves explicit non-surjectivity of the ambient evaluation maps.

## New reusable result

`strictNegative_of_uniformQuadraticRemainder` is a general finite-dimensional perturbation theorem. If a negative weighted diagonal has a strict lower weight margin and a real quadratic remainder is uniformly bounded in absolute value by a smaller multiple of Euclidean coefficient energy, the full form remains strictly negative on every nonzero vector.

This theorem is independent of zeta-specific definitions and is a candidate for later extraction to a more general finite Hermitian-form or Mathlib-facing module after API stabilization.

## Remaining analytic obligation

The four-node chain deliberately leaves one nontrivial input explicit:

```text
HasUniformMultiOrbitRemainderBound F epsilon
```

The next target, `MultiOrbitBurnolUniformRemainder`, should derive this predicate from closed-strip Fourier-Laplace decay, convolution-power amplification, finite exceptional-set interpolation, and absolute zero summability. The estimate must be uniform over every coefficient vector in the fixed finite frame and must control cross terms, not only basis directions.
