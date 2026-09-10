# AffineChart

## Abstract

Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.

**Definition 1.1 (psi).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.psi`

*Formalization.* `D5/S3/HardCoreHolomorphic/AffineChart.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive real message is extended as this affine complex polynomial.

**Definition 1.2 (chart).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.chart`

*Formalization.* `D5/S3/HardCoreHolomorphic/AffineChart.chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A single logarithm suffices. On the positive real interval this is `log (x / (b-a*x)) / b`. The principal branch is used only on the slit plane.

**Definition 1.3 (inverse).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.inverse`

*Formalization.* `D5/S3/HardCoreHolomorphic/AffineChart.inverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Explicit exponential inverse, valid also when `a=0`.

**Definition 1.4 (center).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.center`

*Formalization.* `D5/S3/HardCoreHolomorphic/AffineChart.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real center of the complex neighborhood.

**Theorem 1.5 (inverse hasDerivAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.inverse_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.inverse_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse has the actual complex derivative `x*(b-a*x)`.

**Theorem 1.6 (chart hasDerivAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.chart_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.chart_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual holomorphic chart derivative, with branch and pole assumptions explicit.

**Theorem 1.7 (exp center).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.exp_center`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.exp_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exponentiating the real chart identifies the odds exactly.

**Theorem 1.8 (inverse center).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.inverse_center`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.inverse_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse returns every real interval point exactly.

**Theorem 1.9 (center eq chart).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.center_eq_chart`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.center_eq_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real chart and principal complex chart agree on the positive branch.

**Theorem 1.10 (chart inverse).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.chart_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.chart_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse is two-sided on the principal branch strip. This is the local coordinate identity needed for genuine conjugation, rather than only recovery of one real anchor.

**Theorem 1.11 (inverse odds).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.inverse_odds`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.inverse_odds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projective odds are multiplied by the exponential under coordinate translation. This identifies the exact representation that connects additive shifts and multiplication.

**Definition 1.12 (projective).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.projective`

*Formalization.* `D5/S3/HardCoreHolomorphic/AffineChart.projective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fractional-linear action of the matrix `[[E,0],[k*(E-1),1]]` on its pole-free affine chart.

**Theorem 1.13 (projective mul).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.projective_mul`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.projective_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projective flow obeys the multiplicative composition law on its pole-free chart.

**Theorem 1.14 (projective matrix defect).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.projective_matrix_defect`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.projective_matrix_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct type ratios have a genuine noncommutative matrix defect. The matrices are [[E,0],[k*(E-1),1]] and [[F,0],[l*(F-1),1]].

**Theorem 1.15 (odds amplitude phase).**

Lean statement: `D5/S3/HardCoreHolomorphic/AffineChart.odds_amplitude_phase`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AffineChart.odds_amplitude_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real shifts scale the odds modulus; imaginary shifts rotate its phase. No probability-amplitude or quantum-measurement interpretation is assumed.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.center`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.center_eq_chart`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.chart`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.chart_hasDerivAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.chart_inverse`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.exp_center`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.inverse`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.inverse_center`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.inverse_hasDerivAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.inverse_odds`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.odds_amplitude_phase`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.projective`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.projective_matrix_defect`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.projective_mul`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AffineChart.psi`
