# Sublattice cell count

## Abstract

Sublattice cell count.

**Definition 1.1 (Norm-residue count, abbreviation).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidue`

*Formalization.* `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidue` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Norm-residue count, abbreviation. cardNormLeResidue K c a N is the number of nonzero integral ideals of 𝓞 K of norm ≤ N whose norm is ≡ a (mod c). The leading constant of its effective estimate (exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le) is, by the normalized-error limit of cardNormLeResidue K c a N / N.

**Definition 1.2 (Per-class norm-residue count).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClass`

*Formalization.* `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClass` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Per-class norm-residue count. The number of nonzero integral ideals of 𝓞 K of norm ≤ N, norm residue y (mod c), and ideal class C.

**Definition 1.3 (𝔟-divisible per-class norm-residue count).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClassDvd`

*Formalization.* `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClassDvd` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

𝔟-divisible per-class norm-residue count. The number of nonzero integral ideals of 𝓞 K divisible by 𝔟, of norm ≤ N, norm residue y (mod c), and ideal class D.

**Theorem 1.4 (Coprime ideal-class representative).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.exists_mk0_eq_absNorm_coprime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.exists_mk0_eq_absNorm_coprime` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Every ideal class of a number field has a nonzero integral representative whose absolute norm is coprime to a prescribed positive integer.

## References

- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidue`
- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClass`
- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.cardNormLeResidueClassDvd`
- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer.exists_mk0_eq_absNorm_coprime`
- Dependency: [D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCells](IdealCongruenceCountCells.md)
