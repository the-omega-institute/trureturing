# Rational Interval Expression Certificates

## Abstract

Exact rational arithmetic checks provide proof inputs for real analytic covers.

**Definition 1.1 (Arithmetic expression with proposed endpoints).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The syntax stores rational annotations while the underlying expression retains real semantics.

**Definition 1.2 (Proposed rational bounds).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This projection has no truth authority by itself. The check validates it.

**Definition 1.3 (Real evaluation independent of annotations).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.value`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation discards every endpoint and applies the actual real field operations.

**Definition 1.4 (Exact local rational checks).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.check`

*Formalization.* `D5/S0/Certificates/BoxCover/RationalIntervalExpression.check` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four multiplication corners, square sign cases and strict reciprocal guards are checked recursively.

**Theorem 1.5 (Successful checks enclose every real input).**

Lean statement: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Structural induction proves a real enclosure from only exact rational local comparisons and membership in the input box. No enclosure oracle, external PASS or rational-only input restriction is assumed.

## References

- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.check`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses`
- Truth anchor: `D5/S0/Certificates/BoxCover/RationalIntervalExpression.value`
