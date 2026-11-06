# Exceptional-19 physical zero pairs

## Abstract

An infinite exceptional-19 family of physical zero pairs with strictly negative physical intersection.

For every natural r, set d = 18r + 12, B = 2^d, g = B - 1 and t = g(2B - 3). Keep all labels in the original physical Fin(3d) domain. Select labels by the literal Nat.testBit filters for Q = (B^2 + B + 1)/19 and 2Q.

**Theorem 1.1 (Two literal zero sums and a negative intersection).**

Lean statement: `D5/S3/Combinatorics/Circle/MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two selected physical sums are exactly zero for every r, including r = 0. Their literal physical intersection satisfies the exact 511 identity and is strictly negative. The proof reconstructs the Nat-to-Int source parameters, the 18-bit block carries, and the bounded-mask sum from the actual centered source.

This is a non-Boolean consequence: zero-sum families are not closed under physical intersection. Any all-d intersection-closure criterion is only an application after the exact arithmetic and source-width prerequisites; it is outside this theorem's scope.

The Reg mirror observes the literal actualSource at every physical Fin(3d) state, retains the complete theorem telescope, and records source selection, variation, sensitivity, and continuation unknown. Native reconstruction remains unresolved until the source-bound selector evidence is accepted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
