# Four-Point Power Defect

## Abstract

Four symmetric exponential points have a hyperbolic-trigonometric power defect.

**Theorem 1.1 (The four power defects collapse to a real product).**

$$\operatorname{Defect}(q, \theta, k) = 4\cdot(1 - \operatorname{cosh}(kq)\cdot\operatorname{cos}(k\theta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/FourPointPowerDefect.four_point_power_defect_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real q and theta, the four points are exp(q + i theta), exp(q - i theta), exp(-q + i theta), and exp(-q - i theta). Defect(q, theta, k) is the sum of 1 - z^k over these points.

The power-of-exponential identity moves k into each exponent. The two angular signs cancel the sine terms, while the two radial signs combine into twice the hyperbolic cosine.

This records only the four-point algebraic identity from the source atom. Its detection estimate, asymptotic formula, reciprocal-power expansion, measure interpretation, and numerical certificates are not claimed.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/FourPointPowerDefect.four_point_power_defect_eq`
