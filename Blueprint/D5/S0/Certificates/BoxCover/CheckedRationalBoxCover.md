# Checked Rational Box Covers

## Abstract

An executable rational forest supplies locally justified proofs for a continuous residual-sublevel cover.

**Definition 1.1 (Typed cover, exclusion and split instructions).**

Lean statement: `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.Step`

*Formalization.* `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.Step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Instruction indices are finite, but the covered input space consists of real vectors. A split records two children. Unsupported contractor instructions are not silently accepted.

**Definition 1.2 (Check all arithmetic, expression identities and closed split inclusions).**

Lean statement: `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checkForest`

*Formalization.* `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checkForest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The check recomputes rational expression bounds, compares residual syntax after removing endpoint annotations, and verifies strict child order and inclusion of both closed halves. It does not consume an external success report.

**Theorem 1.3 (An accepted forest covers every real sublevel point in a root box).**

Lean statement: `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checked_forest_covers_sublevel`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checked_forest_covers_sublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RationalIntervalExpression supplies each numerical real enclosure. Expression erasure binds it to the specified residual, and exact endpoint comparisons retain both split halves. These results construct the actual LocalStep proof terms consumed by FiniteSublevelCover.

The theorem supplies no Krawczyk contraction adapter and makes no claim about the full MUB phase-domain instance. Each physical application must still identify the expression semantics with its actual residual. Kernel acceptance requires compiling the source and the concrete data checks.

## References

- Truth anchor: `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.Step`
- Truth anchor: `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checkForest`
- Truth anchor: `D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checked_forest_covers_sublevel`
- Dependency: [D5/S0/Certificates/BoxCover/FiniteSublevelCover](FiniteSublevelCover.md)
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](RationalIntervalExpression.md)
