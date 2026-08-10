# Equal-Ratio Moran Complex Dimensions

## Abstract

The equal-ratio Moran dimension extends to a log-periodic ladder of complex solutions.

**Theorem 1.1 (The Moran equation holds on the complex dimension ladder).**

$$D=\frac{\log M}{k \log \varphi},\qquad s_{n}=D+\frac{2\pi i n}{k \log \varphi},\quad n\in\mathbb{Z},\qquad M\cdot\varphi^{-ks_{n}}=1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MoranComplexDimensions.moran_complex_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural M and k and real phi greater than one, the real Moran dimension is log M divided by k log phi. Adding each integer multiple of 2 pi i divided by k log phi leaves the complexified equal-ratio Moran equation unchanged, producing its log-periodic tower of solutions.

## References

- Truth anchor: `D5/S3/Constants/MoranComplexDimensions.moran_complex_dimension`
