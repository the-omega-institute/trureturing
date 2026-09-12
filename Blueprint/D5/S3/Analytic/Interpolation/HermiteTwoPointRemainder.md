# Two-point Hermite remainder

## Abstract

Two-point Hermite interpolation has a cubic remainder, and a positive third derivative fixes its sign.

**Theorem 1.1 (Cubic remainder and strict sign).**

$$f - p = \frac{\operatorname{iteratedDeriv}\left(3, f\right)}{6} \times {x-L)}^{2} \times {x-H)} , f - p < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteTwoPointRemainder.hermite_two_point_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an interior point between two ordered nodes, a function and its Hermite interpolant agree through first order at the left node and agree in value at the right node. Repeated applications of Rolle's theorem produce an interior point where the third derivative determines the remainder. The cubic factor has a squared left factor and a negative right factor, so a positive third derivative gives a strict negative remainder.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteTwoPointRemainder.hermite_two_point_remainder`
