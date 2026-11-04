# PairedIdealIntersectionCongruence

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Theorem 1.1 (Nilpotent characteristic transport).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.shifted_tensor_charpoly_mod_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.shifted_tensor_charpoly_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Over any commutative ring R of characteristic three, suppose b+1 and c+1 are nilpotent, with arbitrary nilpotency orders. Put X=(F_b+I) tensor I and Y=I tensor(F_c+I). Their squares are (b+1)I and (c+1)I, so X and Y are nilpotent. They commute and K2+I=X+Y-XY; the existing commuting nilpotent sum, product and subtraction laws give nilpotence of K2+I. Its characteristic polynomial differs from the fourth power of the polynomial variable by a nilpotent polynomial. The infinite mod-nine consumer specializes this general law to the reduced field F3, where that difference is zero. Nonreduced rings and unbounded nilpotent thickenings are included in the provider statement.

**Theorem 1.2 (The whole infinite family excludes divisibility by 27).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.shifted_tensor_det_not_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.shifted_tensor_det_not_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For b=9s+5,c=9t+8, the symbolic determinant is 27W+18 for an integer polynomial W. Equivalently, with b=3u-1,c=3v-1, r=u+v,z=uv, it is 36(90z squared+57zr-5r squared+44z+r+2); the bracket is two modulo three. Hence 27 never divides the determinant in this entire family.

**Theorem 1.3 (Infinite-family noninteger real spectrum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.two_mod_nine_noninteger`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.two_mod_nine_noninteger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For positive b=9s+5 and c=9t+8, suppose all real symmetric eigenvalues were integers. The nilpotent characteristic reduction makes every shifted integer root divisible by three. Their product would then be divisible by 3 to the fourth power, contradicting the preceding determinant formula. Positive diagonal transport supplies a noninteger real eigenvalue of the original weighted tensor. The pair (5,8) is the specialization s=t=0; exchanging the tail coordinates covers (8,5). No fixed mod-17 success certificate is used.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.shifted_tensor_charpoly_mod_three`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.shifted_tensor_det_not_dvd`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.two_mod_nine_noninteger`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants](PairedIdealIntersectionDeterminants.md)
