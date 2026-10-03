# The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟)

## Abstract

The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟).

**Theorem 1.1 (The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟)).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountConeDvd.exists_card_idealSet_residue_real_le_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountConeDvd.exists_card_idealSet_residue_real_le_dvd` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The J- and 𝔟J-cone residue counts share a leading constant up to N(𝔟). For gcd(N(𝔟), m) = 1, there is a common κ = ∑_cells L_J with both the J-cone count ≈ κ·S and the 𝔟J-cone count ≈ (κ/N(𝔟))·S (same O(S^{1-1/d}) rate). The two per-cell estimates (exists_card_residue_fibre_sub_mul_rpow_le_explicit, exists_card_fibre_dvd_residue_sub_mul_rpow_le) carry the explicit per-cell constants L_J(p) and L_J(p)/N(𝔟); summing over the (orthant, coset) partition at tN = S^{1/d} gives the result.

## References

- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountConeDvd.exists_card_idealSet_residue_real_le_dvd`
- Dependency: [D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdFibre](IdealCongruenceCountDvdFibre.md)
