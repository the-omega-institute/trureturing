# Full Lebesgue translation energy

## Abstract

Full Lebesgue translation energy.

**Theorem 1.1 (Cell integration).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_canonical_cell_integral_encloses`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_canonical_cell_integral_encloses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a successful canonical cell check and the exact literal Weil test, the cell length times the rational integrand bounds encloses the real interval integral of the squared translation difference. Continuity supplies interval integrability.

**Theorem 1.2 (Whole-line enclosure).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_literal_translation_energy_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_literal_translation_energy_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational polynomials p and q represented by the supplied lists and any rational shift s, checkFull verifies one payload for every adjacent source cell, exact hull endpoints, all cell checks and the requested binary width.

A successful check encloses the genuine whole-line Lebesgue translationEnergy of any WeilTestFunction equal pointwise to the literal cutoff times the even polynomial. Adjacent interval integrals telescope, and the integrand vanishes outside the support hull. The aggregate rational width is at most 2^-k.

The same module constructs literalRationalTest for every positive natural radius and rational p and q. Its smoothness follows from the smooth bump construction, its support lies in [-2R,2R], and its value is even.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_canonical_cell_integral_encloses`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_literal_translation_energy_sound`
- Dependency: [D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound](../LiteralRationalPrimeTranslationBound.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Cell](Cell.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Geometry](Geometry.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/SignedSquares](SignedSquares.md)
