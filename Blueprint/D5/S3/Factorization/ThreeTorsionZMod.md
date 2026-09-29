# Three-Torsion Coordinates Modulo 3m

## Abstract

The three-torsion subgroup of the cyclic modulus 3m has three elements.

The modulus is 3m with m a positive natural number. All equalities in the displayed statement are in ZMod(3m).

**Theorem 1.1 (Exact three-torsion coordinates).**

$$3x = 0 \iff x \in \{0, m, 2m\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ThreeTorsionZMod.three_nsmul_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a representative in [0,3m), the equation 3x=0 is equivalent to m dividing that representative. The only possibilities are 0, m, and 2m.

## References

- Truth anchor: `D5/S3/Factorization/ThreeTorsionZMod.three_nsmul_eq_zero_iff`
