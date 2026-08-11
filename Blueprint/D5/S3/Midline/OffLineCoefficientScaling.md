# Off-Line Coefficient Scaling

## Abstract

Off-line coefficients split into density, phase, and scaling factors.

**Theorem 1.1 (Coefficients split into density, phase, and scaling factors).**

$$s=\frac{1}{2}+\Delta+it,\quad e^{-s\ell}=e^{-\frac{1}{2}\ell}\cdot e^{-it\ell}\cdot e^{-\Delta\ell},\quad\operatorname{scalingLedger}=\Delta\ell.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/OffLineCoefficientScaling.off_line_coefficient_scaling_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a spectral parameter with real displacement `delta`, each labeled coefficient factors into its critical half-density, unitary phase, and real scaling terms. The scaling ledger is exactly `delta * length`; when `delta` is nonzero the existing growth theorem supplies nonvanishing, common sign, natural scaling, and unboundedness on every positive-length address.

Multiplication by any complex unit preserves the coefficient's norm. These are coordinatewise statements only and do not assert anything about cancellation after analytic continuation.

## References

- Truth anchor: `D5/S3/Midline/OffLineCoefficientScaling.off_line_coefficient_scaling_spec`
- Dependency: [D5/S3/Midline/OffLineScaling](OffLineScaling.md)
