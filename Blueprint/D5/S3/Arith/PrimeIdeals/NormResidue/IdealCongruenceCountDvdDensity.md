# The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1)

## Abstract

The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1).

**Theorem 1.1 (The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1)).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdDensity.cardNormLeResidueClassDvd_div_density`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdDensity.cardNormLeResidueClassDvd_div_density` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The dvd-density is the full density divided by N(𝔟) (Lang VI §3 Thm 3; GRS Thm 1). For a realizer 𝔟 with N(𝔟) (mod c) a unit, the 𝔟-divisible class-D norm-residue count has density κfull/N(𝔟), where κfull is the full class-D residue-y density. Proved the geometric (covolume / CRT-equidistribution) way: principalize both counts at a coprime representative J of D⁻¹ and read off the index-N(𝔟) sublattice scaling from the shared cone estimate exists_card_idealSet_residue_real_le_dvd.

## References

- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdDensity.cardNormLeResidueClassDvd_div_density`
- Dependency: [D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountConeDvd](IdealCongruenceCountConeDvd.md)
