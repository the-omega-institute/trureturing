# Four-path Section 71 finite floor certificate

## Abstract

The seven rational majorants in the Section 71 four-path estimate are uniformly below the common floor 49359/40000.

**Definition 1.1 (Section 71 non-radical segment bounds).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentNonroot`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentNonroot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven entries are the non-radical upper bounds in equation (71.8) of the repository's Continuation VI theory volume.

**Definition 1.2 (Section 71 radical segment bounds).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentRadical`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentRadical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven entries are the radical upper bounds in equation (71.8), recorded as exact positive rationals.

**Theorem 1.3 (Finite segment majorants below the common floor).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every one of the seven rows, the recorded non-radical and radical bounds sum to a value strictly below 49359/40000. The result is the finite rational arithmetic core of Section 71.

The complete negative-row theorem FourPathNegativeFloor.negative_floor applies these comparisons to the actual radical support bounds on the closed triangle and combines them with the strict energy threshold. The rational table alone makes no assertion about the original defect.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentNonroot`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentRadical`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor`
