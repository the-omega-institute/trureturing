# Mirror-Pair Identity

## Abstract

Applying reflected conjugation twice returns the original complex coordinate.

**Theorem 1.1 (Reflected conjugation is an involution).**

$$\forall \rho\in\mathbb{C},\ 1 - \overline{1 - \overline{\rho}} = \rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/MirrorPairIdentity.mirror_pair_involution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex coordinate rho, applying the map rho maps to 1 minus its conjugate twice returns rho. The result is the algebraic involution underlying mirror-pair arguments; it does not assert that either coordinate is a zeta zero.

## References

- Truth anchor: `D5/S3/Zeros/MirrorPairIdentity.mirror_pair_involution`
