# Signed Mangoldt masses at fourth-power samples

## Abstract

Fourth-power samples recover either signed Mangoldt mass up to a logarithmic error.

**Theorem 1.1 (Logarithmic error for either sign).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.quartic_grid_log_error`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.quartic_grid_log_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural numbers 1 ≤ A ≤ B and a real multiplier s with |s| ≤ 1, let Q be the sum of the weighted positive parts of the affine chords of sU between consecutive fourth powers from A⁴ to B⁴. The weight is x^(−3/2). The absolute difference between Q and the weighted positive mass of sU is at most 4275(log B − log A) + 3375/A + 225(log 4 + 6).

An arithmetic hinge contributes to the interpolation error only when its knot lies strictly inside the cell. Integrating the cell error charges at most 3375/n for the logarithmic curvature and 225 times the sum of Λ(k)/k over the interior knots. The harmonic sum and the weighted Mangoldt sum give the uniform logarithmic bound.

**Theorem 1.2 (Power growth on every sufficiently late block).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.off_line_zero_forces_signed_quartic_chord_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.off_line_zero_forces_signed_quartic_chord_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If ζ has a zero with real part β > 1/2, then for each ε > 0, on every sufficiently late block of fourth powers with indices from k³ to k⁴, each signed chord mass is at least k^(16(β − 1/2) − ε). The same threshold in k works for both signs.

The complete Chebyshev tail identity identifies the signed integral with the continuous mass in the existing pole-growth theorem. The latter is applied on the power window from k¹² to k¹⁶ with a smaller exponent loss. That smaller loss absorbs the logarithmic chord error.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.off_line_zero_forces_signed_quartic_chord_mass`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.quartic_grid_log_error`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace](CompleteMangoldtLaplace.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth](PrimeWindowPoleGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling](QuarticSampling.md)
