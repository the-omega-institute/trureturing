# Effective coset lattice-point count

## Abstract

Effective coset lattice-point count.

**Theorem 1.1 (Effective coset lattice-point count).**

Lean statement: `D5/S3/Arith/Lattices/Counting/IdealCongruenceCountRealScale.exists_card_coset_inter_smul_sub_volume_mul_rpow_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Counting/IdealCongruenceCountRealScale.exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Effective coset lattice-point count (Widmer / GRS Theorem 3 as used; the translate- and-transport closure of L1). For a full lattice T '' ℤ^ι (T a linear automorphism of ι → ℝ) and a bounded measurable region D whose frontier is covered by finitely many Lipschitz images of the unit cube, the number of points of any coset ξ + T '' ℤ^ι in the real dilation t • D is vol D / |det T| · t ^ d + O(t ^ (d-1)), with the implied constant uniform in the translate ξ (it depends only on the cover data and T, as the L1 constant depends only on the cover data).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Counting/IdealCongruenceCountRealScale.exists_card_coset_inter_smul_sub_volume_mul_rpow_le`
- Dependency: [D5/S3/Arith/Lattices/Counting/LatticePointCount](LatticePointCount.md)
