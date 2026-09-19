# Spatial cutoff interval widths

## Abstract

Spatial cutoff interval widths.

**Theorem 1.1 (Two scalar endpoints).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.cutoffInterval_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.cutoffInterval_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For ordered rational arguments ta<=tb and every natural precision m, the two exact scalar intervals give an ordered enclosure contained in [0,1]. Its width is at most 9(tb-ta)+2*2^-m, using the global nine-Lipschitz bound for the smooth transition.

**Theorem 1.2 (An entire shifted cell).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.shiftedCutoffInterval_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.shiftedCutoffInterval_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive rational radius r, an ordered rational cell [a,b], rational translation c and natural precision m, the constructed interval encloses smoothTransition(2-|x+c|/r) for every real x in that cell. Its width is at most 9(b-a)/r+2*2^-m, and its endpoints remain in [0,1].

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.cutoffInterval_certificate`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.shiftedCutoffInterval_certificate`
- Dependency: [D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound](../LiteralRationalPrimeTranslationBound.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform](Scalar/Uniform.md)
