# Fibre

## Abstract

Native local sequences lift over literal fixed fibres using the existing coordinate homotopy.

**Definition 1.1 (liftFibre).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Fibre.liftFibre`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Fibre.liftFibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Non-VOID local sequences lift over a literal fibre. This is used for Gamma and filling/collar schedules; all ordinary lower faces are still nonempty even when a=empty. No homotopy or parent certificate is an input. 

**Theorem 1.2 (liftFibre_pairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Fibre.liftFibre_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Fibre.liftFibre_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact ordered coverage for the ACTUAL native fibre list, including every pair of a supplied Gamma, filling-main or separate collar sequence. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Fibre.liftFibre`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Fibre.liftFibre_pairs`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Certificates](Certificates.md)
