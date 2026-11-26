# The restricted derivative recurrence

## Abstract

The restricted derivative gives an all-order recurrence for the concrete section jets.

**Theorem 1.1 (The correction has zero second derivative).**

Lean statement: `D5/S3/Arith/CMJet/Correction.correction_second`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Correction.correction_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary and restricted derivations commute on S. Cancelling S gives the derivative of the correction, whose next derivative vanishes by the base scalar law.

**Theorem 1.2 (Recurrence for the integer section jets reduced at an odd prime).**

Lean statement: `D5/S3/Arith/CMJet/Correction.integer_jet_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Correction.integer_jet_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection forces the correction to vanish at the origin. The product rule then retains only the first derivative of the correction. The two scalar coefficients are given by iterates on the original curve.

## References

- Truth anchor: `D5/S3/Arith/CMJet/Correction.correction_second`
- Truth anchor: `D5/S3/Arith/CMJet/Correction.integer_jet_recurrence`
- Dependency: [D5/S3/Arith/CMJet/JetReduction](JetReduction.md)
