# The L2 count as a sum of norm-residue counts

## Abstract

The L2 count as a sum of norm-residue counts.

**Theorem 1.1 (The original per-prime cyclotomic character formula).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.autToPow_frobeniusClass`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.autToPow_frobeniusClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero prime ideal unramified in a cyclotomic extension and with norm coprime to the modulus, the primitive-root character of its Frobenius class representative is the unit represented by its absolute norm. This is the existing per-prime proof factored from the ideal formula, which continues to consume it.

**Definition 1.2 (Is Bad Part).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.IsBadPart`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.IsBadPart` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The "bad-supported" ideals of norm ≤ N: nonzero, with every prime factor unramified in L and of norm not coprime to m.

**Definition 1.3 (bad Finset).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.badFinset`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.badFinset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ideals supported on unramified primes whose norm is not coprime to m, bounded by N.

**Theorem 1.4 (The L2 count as a sum of norm-residue counts).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.card_L2_eq_sum_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.card_L2_eq_sum_residue` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The L2 count as a sum of norm-residue counts. Chaining the finite bad-part partition, the per-bad-part bijection (card_fibre_eq_card_good_fibre), and the good- fibre↔residue dictionary (card_good_fibre_eq_card_residue): the L2 fibre count at g is the sum over the finite bad-part set of the norm-residue counts of modulus m at residue autToPow (g · Frob(𝔟)⁻¹), each up to norm ⌊N / N𝔟⌋.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.IsBadPart`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.autToPow_frobeniusClass`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.badFinset`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.card_L2_eq_sum_residue`
- Dependency: [D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic](ZetaProductArithmetic.md)
