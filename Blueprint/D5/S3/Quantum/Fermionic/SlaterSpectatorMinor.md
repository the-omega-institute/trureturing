# Ordered Slater minors with an appended orbital

## Abstract

Ordered Slater minors with an appended orbital

**Definition 1.1 (Appending a coordinate orbital).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.appendOrbital`

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.appendOrbital` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex site-by-orbital matrix V and a site p in the linearly ordered site type, append a last column with entry one at p and zero elsewhere. The other columns retain their order and entries.

**Definition 1.2 (The minor on an occupied set).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.occupiedMinor`

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.occupiedMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite set S of sites and a complex site-by-orbital matrix with k columns, take the determinant of the rows of S in increasing site order when S has size k. For every other size the value is zero.

**Theorem 1.3 (The cofactor of the appended coordinate).**

Lean statement: `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.occupiedMinor_append`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.occupiedMinor_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite occupied set S, the minor for the appended matrix vanishes when p is absent from S. When p is present, it equals the original occupied minor on S with p removed, times minus one to the power of the number of elements of S strictly greater than p. The removal preserves the increasing enumeration of the other rows. The cofactor position in the last column has this parity for every occupied set of the matching size, and the zero convention gives the formula for all other sizes.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.appendOrbital`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.occupiedMinor`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterSpectatorMinor.occupiedMinor_append`
