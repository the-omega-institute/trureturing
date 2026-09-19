# Rational Horner interval factories

## Abstract

Rational Horner interval factories.

**Theorem 1.1 (Structural checker acceptance).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_check`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ordered rational interval and finite coefficient list, the recursively constructed Horner expression passes the annotated rational expression checker. The singleton case is a constant expression; longer lists multiply the tail by the input and add the leading coefficient.

**Theorem 1.2 (Amplitude and width budgets).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_interval_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_interval_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an interval [a,b] contained in [-B,B], the Horner enclosure for coefficients cs lies in [-A(cs),A(cs)] and has width at most D(cs)(b-a). The recurrences are A(c::cs)=|c|+B A(cs) and D(c::cs)=A(cs)+B D(cs), with zero empty-list budgets.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_check`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_interval_bounds`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Polynomial/ProductIntervals](ProductIntervals.md)
