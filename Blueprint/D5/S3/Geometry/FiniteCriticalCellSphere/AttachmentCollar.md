# The attachment collar and core quotient

## Abstract

The attachment collar and core quotient.

The input retains the original ambient labels, a nonempty attached face, the exact union with its simplex and full-boundary intersection, and only a standalone based contraction of the core. Closed radial and attachment pasting constructs the collar, its endpoint quotient inverse and both homotopies fixing the retained basepoint.

**Definition 1.1 (diskRestrict).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict an actual disk-set point to its original simplex coordinates.

**Theorem 1.2 (diskIn_restrict).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inclusion after restriction is the original actual attachment point.

**Theorem 1.3 (restrict_diskIn).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction after disk inclusion is the original simplex point.

**Theorem 1.4 (cover).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual attachment point is in the core or its attached simplex.

**Theorem 1.5 (core_closed).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The included original core is closed in the attachment.

**Theorem 1.6 (disk_closed).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The attached original simplex is closed in the attachment.

**Theorem 1.7 (diskIn_mem_core_iff).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disk inclusion is in the core exactly on the full simplex boundary.

## References

- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.core_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cover`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_mem_core_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn_restrict`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskRestrict`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.disk_closed`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.restrict_diskIn`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](../FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteSimplexBoundarySphere](../FiniteSimplexBoundarySphere.md)
