# A rational enclosure at log two

## Abstract

A rational enclosure at log two.

**Theorem 1.1 (The exact rational center).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the radius-one literal test with p=q=1 and rational shift 287209/414355, the actual rounded producer uses mesh depth 15, scalar precision 16 and Taylor depth 68. The full Boolean checker succeeds at requested binary precision 4.

The value at zero is exactly 1+i. The actual rational aggregate endpoints enclose the full translation energy, the lower endpoint is strictly positive, and the width is at most 115/2048+5/268435456. This is strictly below 1/16. The positive lower endpoint follows from the analytic energy lower bound and the accepted width.

**Theorem 1.2 (Two-sided logarithmic inflation).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.log_two_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.log_two_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define logTwoBox by subtracting 1152/10^10 from the actual center lower endpoint and adding the same amount to its upper endpoint. The resulting rational interval encloses the energy at the actual real shift log 2, has strictly positive lower endpoint and width strictly less than 1/16.

The shift-transfer coefficient specializes to 1152, and Real.log_two_near_10 bounds the center error by 10^-10. The total inflation is 2304/10^10. The theorem also retains the exact value at zero and the successful full center check.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.log_two_certificate`
- Dependency: [D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound](../../LiteralRationalPrimeTranslationBound.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Unit/Width](Width.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/UnitLowerBound](../UnitLowerBound.md)
