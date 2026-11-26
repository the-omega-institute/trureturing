# Binary cubic forms with a repeated root

## Abstract

Idempotence distinguishes the two binary forms with characteristic polynomial X cubed plus X.

**Theorem 1.1 (The two forms on the primary space at one).**

Lean statement: `D5/S1/Eigenstructure/BinaryCubicRepeatedRoot.exists_basis`

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/BinaryCubicRepeatedRoot.exists_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f act on a three-dimensional vector space over the binary field with characteristic polynomial X cubed plus X. There is an ordered basis b0, b1, b2. The operator fixes b0 and sends b2 to zero. It fixes b1 if f is idempotent and sends b1 to b0 plus b1 otherwise.

The eigenvalue zero is a simple root of the characteristic polynomial, so the kernel has dimension one. Cayley–Hamilton gives f cubed equal to f, making the square the projection onto the complementary two-dimensional space. There f is an involution. An involution different from the identity minus the identity is a nonzero square-zero map. A vector with nonzero image and that image supply the length-two block.

These two forms give the scalar and Jordan types in the Heawood double cover classification. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108

## References

- Truth anchor: `D5/S1/Eigenstructure/BinaryCubicRepeatedRoot.exists_basis`
