# Midslope Double-Dual Law

## Abstract

Affine duality of the arithmetic and geometric midslope values is exactly reverse doubling of their curvature coefficients.

**Theorem 1.1 (The arithmetic and geometric values satisfy the double-dual law).**

$$J(0) = 2J(1) + 1 \Leftrightarrow \frac{1}{1+J(1)} = 2\frac{1}{1+J(0)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeDoubleDual.arithmetic_geometric_double_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a midslope value j, define its curvature coefficient as c(j) = 1 / (1 + j). Away from the pole j = -1, the identity j' = 2j + 1 is equivalent, by clearing denominators, to the reverse doubling relation c(j) = 2c(j').

The repository already proves J(1) = -log 2 for the arithmetic mean and J(0) = 1 - 2 log 2 for the geometric mean. These exact values make both sides hold, while Mathlib's strict logarithm bound shows that neither curvature denominator vanishes.

This is casewise partial closure of the source corollary. It covers the arithmetic-geometric pair only; the separate logarithmic-harmonic pair remains outside this declaration.

## References

- Truth anchor: `D5/S3/Constants/MidslopeDoubleDual.arithmetic_geometric_double_dual`
- Dependency: [D5/S3/Constants/MidslopeCurvatureValues](MidslopeCurvatureValues.md)
