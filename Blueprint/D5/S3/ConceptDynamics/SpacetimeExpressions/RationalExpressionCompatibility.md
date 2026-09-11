# Expressions on actual rich rational fractions

## Abstract

Expressions on actual rich rational fractions.

Typed Lean handles carry these statements. Formula projection limitations are reported by the canonical Scribe tools; no handwritten formula substitutes for a Lean type. The actual real interpretation and the full shared-world expression theorem remain E2.

**Theorem 1.1 (The native divisor guard is precisely nonzero readout).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.guard_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.guard_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RichRational.division_guard_iff proves this on the actual Fraction d carrier. RichRational.div consumes the proof and constructs a fraction with a nonzero denominator.

**Theorem 1.2 (Readout commutes with every finite native rational expression).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.readout_eval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.readout_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constants use rationalSection and variables range over actual RichRational.Fraction d. The implementation uses exactly RichRational.add, mul, neg and guarded div with their established readout laws.

**Theorem 1.3 (Every intermediate rational division remains guarded).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.legal_iff_all_nodes`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.legal_iff_all_nodes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AllLegal retains every child and each nonzero divisor readout. Rat division being total at zero does not make the partial ordinary expression evaluator total.

**Theorem 1.4 (Legal rich and ordinary rational results have equal values).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.value_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.value_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source value identity follows from equality of the full Option evaluations.

**Theorem 1.5 (Ordinary equality is actual rational quotient equality).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.value_eq_iff_class_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.value_eq_iff_class_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof combines RichRational.cross_iff_readout with RationalQuotient.class_eq_iff on the evaluated native fractions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.guard_iff`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.legal_iff_all_nodes`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.readout_eval`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.value_eq`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.value_eq_iff_class_eq`
- Dependency: [D5/S0/Rewriting/Expressions/GuardedArithmeticTerms](../../../S0/Rewriting/Expressions/GuardedArithmeticTerms.md)
- Dependency: [D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient](../SpacetimeArithmetic/RationalQuotient.md)
