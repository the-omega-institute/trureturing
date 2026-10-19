# Exact numbered positive recoding and inverse time signs

## Abstract

Exact numbered positive recoding and inverse time signs.

For arbitrary rectangular nonnegative matrices R and S, positive_coordinate sends the two half-edges at t to the S half-edge at t joined with the R half-edge at t+1. inverse_coordinate recovers the R half-edge from time t-1 and the S half-edge from time t. translate B a x has coordinate x at t+a for every signed integer a.

positive_translate commutes the literal positive action with signed time. inverse_eq_negative_positive identifies its inverse with the opposite positive recoding followed by translation by -1. Applying this inverse identity and canceling the bijection derives that opposite positive recodings compose to the forward shift. There is no period or nonempty-fiber hypothesis.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Remark 1.1 (translate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.translate`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.translate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer time translation has the literal forward-time sign.

**Remark 1.2 (positive_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_coordinate`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual positive law (r_t,s_t) -> (s_t,r_(t+1)).

**Remark 1.3 (inverse_coordinate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_coordinate`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse has preceding time on the recovered R half-edge.

**Remark 1.4 (positive_translate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_translate`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_translate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual positive elementary recoding commutes with every signed integer translation. Both half-edge coordinates use the same translated time.

**Remark 1.5 (inverse_eq_negative_positive).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_eq_negative_positive`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_eq_negative_positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replacing an inverse by the opposite POSITIVE recoding costs -1.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_eq_negative_positive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_translate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.translate`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap](../CountedMatrixOverlap.md)
