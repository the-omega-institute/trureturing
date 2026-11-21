# Checked resolution blocks for the four-braid

## Abstract

Checked resolution blocks for the four-braid

**Theorem 1.1 (The stored blocks agree with the smoothing calculation).**

Lean statement: `D5/S3/Topology/FourBraidKhovanovResolutionData.snapshot_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FourBraidKhovanovResolutionData.snapshot_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each block of 32 smoothing choices records the maximum quantum grade. For a choice that can contribute at grade 17 or higher, it also records the circle partition. The kernel checks each block against the actual matching calculation, so subsequent matrix checks can reuse those values.

## References

- Truth anchor: `D5/S3/Topology/FourBraidKhovanovResolutionData.snapshot_correct`
- Dependency: [D5/S3/Topology/FourBraidKhovanovCube](FourBraidKhovanovCube.md)
