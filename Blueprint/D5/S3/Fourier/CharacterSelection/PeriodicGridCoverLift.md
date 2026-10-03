# Periodic Grid Cover Lift

## Abstract

Flat periodic binary labels lift uniquely to a twisted integer covering grid.

**Definition 1.1 (Pulled-back horizontal label).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.pulledHorizontal`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.pulledHorizontal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At integer coordinates (i,j), evaluate the periodic horizontal label at the residues of i modulo M and j modulo N.

**Definition 1.2 (Pulled-back vertical label).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.pulledVertical`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.pulledVertical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At integer coordinates (i,j), evaluate the periodic vertical label at the residues of i modulo M and j modulo N.

**Definition 1.3 (Anchored twisted cover lift).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.IsCoverLift`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.IsCoverLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A binary vertex field on all of Z x Z has the prescribed anchor, the two pulled-back adjacent edge differences, and horizontal and vertical period shifts equal to the two holonomies.

**Theorem 1.4 (Unique twisted lift of a flat periodic label).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.flat_unique_cover_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.flat_unique_cover_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M,N at least three, every flat periodic ZMod 2 edge label and every binary anchor have exactly one lift to the integer grid. The lift has the pulled-back edge differences and gains the row or column holonomy under the corresponding period translation. The construction integrates the two seam terms using integer quotients; uniqueness follows from connectivity by unit steps.

The parity-independent horizontal seam with holonomy (1,0) and no periodic vertex gradient is already proved by PeriodicGridHolonomy.horizontal_seam_counterexample.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.IsCoverLift`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.flat_unique_cover_lift`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.pulledHorizontal`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.pulledVertical`
- Dependency: [D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy](PeriodicGridHolonomy.md)
