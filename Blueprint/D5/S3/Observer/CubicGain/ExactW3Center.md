# ExactW3Center

## Abstract

The exact algebraic third critical center

criticalPolynomial is the degree-67 real polynomial whose descending integer coefficient list is the pinned FC list. The rational interval (12758053/100000000,12758054/100000000) has opposite exact endpoint signs, so it contains an exact real root.

critical_root_exists records the degree and constructs a root b3 in that interval by the intermediate value theorem. The root is retained as an algebraic real selected by its defining polynomial and interval, rather than by a decimal approximation.

determinantalLiftDenominator and determinantalLiftNumerator are the reduced linear-subresultant coefficient polynomials from the pinned regular critical elimination. liftedR(b) is the exact quotient -c(b)/a(b), and liftedCoordinates(b) is (liftedR(b)/b,b). exactW3 is the ordinary coefficient-coordinate chartWorld at the selected root.

exactW3_parent_of_source_certificate proves that this exact lift is an OriginalParent and that chartRead is analytic whenever the source-specific rational enclosures and nonzero denominator certificate hold. The chart is the original coefficient topology and keeps the source certificate explicit.

**Theorem 1.1 (exact degree-67 critical root).**

Lean statement: `D5/S3/Observer/CubicGain/ExactW3Center.critical_root_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ExactW3Center.critical_root_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned criticalPolynomial has degree 67 and has a real root strictly between 12758053/100000000 and 12758054/100000000.

**Theorem 1.2 (exact W3 parent bridge).**

Lean statement: `D5/S3/Observer/CubicGain/ExactW3Center.exactW3_parent_of_source_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ExactW3Center.exactW3_parent_of_source_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the selected root's determinantal lift satisfies the displayed original source strip, nonzero denominator and strict-coordinate conditions, then exactW3 is an OriginalParent and chartRead is analytic at its exact lifted coordinates.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/ExactW3Center.critical_root_exists`
- Truth anchor: `D5/S3/Observer/CubicGain/ExactW3Center.exactW3_parent_of_source_certificate`
- Dependency: [D5/S3/Observer/CubicGain/RegularParentChart](RegularParentChart.md)
