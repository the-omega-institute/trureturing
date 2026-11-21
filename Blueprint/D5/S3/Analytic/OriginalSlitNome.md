# Holomorphic continuation from the sewing cusp

## Abstract

The native nome and rank-24 determinant on the Euler slit

**Definition 1.1 (Punctured Euler slit).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.puncturedSlit`

*Formalization.* `D5/S3/Analytic/OriginalSlitNome.puncturedSlit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove the cusp r = 0 from the Euler slit, the domain on which 1 − r lies in the principal slit plane.

**Definition 1.2 (The continued lattice nome).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.slitNome`

*Formalization.* `D5/S3/Analytic/OriginalSlitNome.slitNome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set the nome to zero at the cusp. Off zero use exp(iπτ(r)) on the double slit and the signed Pfaff nome on the negative real axis. The Pfaff jump identifies the two expressions on the overlap of the local Pfaff chart with the double slit. `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negative_real_nome_extension`

**Theorem 1.3 (Agreement with the native disk nome).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_Q0`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_Q0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On |r| < 1 the continuation equals Q₀(r), including at zero. The identity theorem propagates the equality from the lens around r = 1/2 to the slit disk. Continuity then extends the equality to the negative real points of the disk. `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_source`

**Theorem 1.4 (The period-ratio expression).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every point of the double slit the glued nome equals exp(iπτ(r)). This is the expression used to compare the nome to a D-lip branch.

**Theorem 1.5 (Holomorphy on the Euler slit).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.slitNome_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalSlitNome.slitNome_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential formula is holomorphic on the double slit. Near each negative real point, the glued nome agrees with the holomorphic signed Pfaff chart. At the cusp, equality on the disk transfers holomorphy from Q₀. `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_disk`

**Theorem 1.6 (Strict unit-disk bound).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.slitNome_norm_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalSlitNome.slitNome_norm_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nome has modulus strictly below one throughout the Euler slit. The exponential has modulus exp(−π Im τ) on the double slit. The Pfaff chart supplies the same strict bound on the negative real axis, and zero covers the cusp.

**Definition 1.7 (Rank-24 determinant factor).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.rank24Determinant`

*Formalization.* `D5/S3/Analytic/OriginalSlitNome.rank24Determinant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the Euler period P, the rank-24 scalar factor is (1 − r)⁻³ P(r)⁻¹². Both powers have integral exponents.

**Theorem 1.8 (Holomorphy of the determinant factor).**

Lean statement: `D5/S3/Analytic/OriginalSlitNome.rank24Determinant_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalSlitNome.rank24Determinant_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factor is holomorphic at every point of the Euler slit. The factor 1 − r is nonzero there, and the Euler period is holomorphic and nonzero. `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_analyticOnNhd`, `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_ne_zero`

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_disk`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_source`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negative_real_nome_extension`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_analyticOnNhd`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.slitPeriod_ne_zero`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.puncturedSlit`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.rank24Determinant`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.rank24Determinant_analyticOnNhd`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_analyticOnNhd`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_Q0`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_eq_exp`
- Truth anchor: `D5/S3/Analytic/OriginalSlitNome.slitNome_norm_lt_one`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialNome](OriginalHalfBinomialNome.md)
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialPfaffNome](OriginalHalfBinomialPfaffNome.md)
