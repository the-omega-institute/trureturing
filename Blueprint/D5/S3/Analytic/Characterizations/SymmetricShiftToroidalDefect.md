# Symmetric-Shift Toroidal Hermite-Biehler Defect

## Abstract

Xi reflection and conjugation identify the symmetric readings by the Hermite-Biehler sharp, while nonzero toroidal frames cancel from their normalized energies.

**Theorem 1.1 (The normalized frame defect is the shifted-xi norm defect).**

$$\forall z, \omega, Tplus, Tminus, \left(0 < \operatorname{Im}\left(z\right) \land \left(0 < \omega \land \left(Tplus \ne 0 \land Tminus \ne 0\right)\right)\right) \Rightarrow \left(\operatorname{xi}\left(\operatorname{s}\left(z\right) - \omega\right) = \operatorname{sharp}\left(\operatorname{Eplus}\left(\omega\right), z\right) \land \left(\frac{1}{2} < \operatorname{Re}\left(\operatorname{s}\left(z\right)\right) \land \operatorname{toroidalHermiteBiehlerDefect}\left(z, \omega, Tplus, Tminus\right) = \left\lVert \operatorname{xi}\left(\operatorname{s}\left(z\right) + \omega\right) \right\rVert^{2} - \left\lVert \operatorname{xi}\left(\operatorname{s}\left(z\right) - \omega\right) \right\rVert^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/SymmetricShiftToroidalDefect.symmetric_shift_toroidal_hermite_biehler_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an upper-half-plane point and a positive shift, each nonzero frame contributes the same squared norm to numerator and denominator, so its factor cancels.

The frozen reflection and conjugation theorems for the completed xi reading identify the minus shift with the Hermite-Biehler sharp of the plus shift.

A concrete one-dimensional frame evaluates the defect to three. Setting the plus frame to zero instead evaluates it to minus one, recording why frame nonvanishing is required.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/SymmetricShiftToroidalDefect.symmetric_shift_toroidal_hermite_biehler_defect`
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](../../Zeros/Symmetry/ZetaConjugationCovariance.md)
