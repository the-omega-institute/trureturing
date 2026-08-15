# Semigroup Relations and Nica Covariance

## Abstract

The address shifts form semigroups whose coprime range projections satisfy Nica covariance.

**Theorem 1.1 (Backward shifts form a semigroup).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{backwardShiftCLM}(u) \circ \operatorname{backwardShiftCLM}(v) = \operatorname{backwardShiftCLM}(\operatorname{normalizedTableAdd}(u, v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/SemigroupRelations.backward_shift_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the backward shifts at u and v pulls a coefficient through two successive address translations. Associativity of multiplication under the prime-axis encoding identifies this with the single shift at their normalized table sum.

**Theorem 1.2 (Forward translations form a semigroup).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{forwardTranslationCLM}(u) \circ \operatorname{forwardTranslationCLM}(v) = \operatorname{forwardTranslationCLM}(\operatorname{normalizedTableAdd}(u, v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/SemigroupRelations.forward_translation_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two zero-extended forward translations have support exactly on the image of the composite address translation. On that image they recover the original coefficient in two stages, and away from it both sides vanish.

**Theorem 1.3 (Coprime range projections satisfy Nica covariance).**

$$\forall u, v\in \operatorname{PrimeAxisTable},\ \operatorname{Coprime}(\operatorname{primeAxisEncoding}(u), \operatorname{primeAxisEncoding}(v)) \Rightarrow \operatorname{shiftRangeProjection}(u) \circ \operatorname{shiftRangeProjection}(v) = \operatorname{shiftRangeProjection}(\operatorname{normalizedTableAdd}(u, v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/NicaCovariance/SemigroupRelations.shift_range_projection_comp_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each range projection is the divisibility filter for one encoded address. When the two encodings are coprime, passing both filters is equivalent to divisibility by their product, which is the encoding of the normalized table sum.

## References

- Truth anchor: `D5/S3/Zeros/NicaCovariance/SemigroupRelations.backward_shift_comp`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/SemigroupRelations.forward_translation_comp`
- Truth anchor: `D5/S3/Zeros/NicaCovariance/SemigroupRelations.shift_range_projection_comp_of_coprime`
- Dependency: [D5/S3/Zeros/ShiftOperators/ShiftRangeProjection](../ShiftOperators/ShiftRangeProjection.md)
