# Dyadic mean square of the Möbius-mollified zeta function

## Abstract

Dyadic mean square of the Möbius-mollified zeta function

**Theorem 1.1 (Uniform power saving on a fixed vertical strip).**

Lean statement: `D5/S3/Weil/MollifiedDyadicMeanSquare.dyadic_mollified_zeta_mean_square`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/MollifiedDyadicMeanSquare.dyadic_mollified_zeta_mean_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a strip with lower edge a strictly between one half and one, put d = a − 1/2 and truncate the Möbius polynomial at floor(T^(d/4)). The integral of the squared mollified error over T − 1 ≤ |t| ≤ 2T + 1 is bounded uniformly by a constant times T^(1−d²/4). The bounds for the finite convolution and the actual zeta truncation control the two contributions on this band.

## References

- Truth anchor: `D5/S3/Weil/MollifiedDyadicMeanSquare.dyadic_mollified_zeta_mean_square`
- Dependency: [D5/S3/Analytic/Asymptotics/DirichletPolynomialMeanSquare](../Analytic/Asymptotics/DirichletPolynomialMeanSquare.md)
- Dependency: [D5/S3/Weil/MollifiedZetaPolynomial](MollifiedZetaPolynomial.md)
- Dependency: [D5/S3/Weil/ZetaTruncationMeanSquare](ZetaTruncationMeanSquare.md)
