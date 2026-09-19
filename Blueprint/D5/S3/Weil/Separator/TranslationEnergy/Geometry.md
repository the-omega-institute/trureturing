# Mass of the canonical partition

## Abstract

Mass of the canonical partition.

**Theorem 1.1 (Total cell length).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_eq_hull`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_eq_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural radius, rational shift and natural depth, summing canonical cell lengths over the actual sourceCells list telescopes to the support hull length. The proof uses the actual first and last source endpoints.

**Theorem 1.2 (Quadratic cell mass).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural radius, the sum of squared cell lengths is at most the maximum dyadic gap times the support hull length. Nonnegative cell lengths allow multiplication of the individual gap bound before summation.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_eq_hull`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_sq_le`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Source](Source.md)
