# Canonical Coordinates for States

## Abstract

States have a lossless five-coordinate presentation with a canonical prime-ledger code.

**Theorem 1.1 (Canonical five coordinates are lossless).**

$$\operatorname{Bijective}(\operatorname{onticStateEquivCoordinates})$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/OnticStateCoordinates.canonical_five_coordinates_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state records a finitely supported prime-exponent ledger, a phase coordinate, a finite readout, and a ledger coordinate. Its fifth coordinate is the positive-natural code determined by the canonical prime-axis encoding. The formal coordinate type carries an equality proof tying that code to the prime ledger, so an arbitrary or stale code cannot inhabit the representation. Forgetting the dependent code and recomputing it gives mutually inverse maps, which makes the source atom's single state definition an explicit lossless equivalence.

The pinned library was searched before construction. It provides Equiv.bijective, Equiv.apply_eq_iff_eq, and Equiv.subtypeEquiv, but no five-coordinate state equivalence tied to the repository's canonical prime-axis encoder. The Lean declaration is therefore a new local constrained-coordinate construction using the existing D5.S1.Digit.primeAxisEncoding, with only the final bundled bijectivity step delegated to Mathlib. The source atom carries no numerical certificate.

## References

- Truth anchor: `D5/S1/Dynamics/OnticStateCoordinates.canonical_five_coordinates_bijective`
- Dependency: [D5/S1/Digit/PrimeAxisEncoding](../Digit/PrimeAxisEncoding.md)
