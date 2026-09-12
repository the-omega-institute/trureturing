# Expressions on actual balanced integer histories

## Abstract

Expressions on actual balanced integer histories.

Typed Lean handles carry these statements. Formula projection limitations are reported by the canonical Scribe tools; no handwritten formula substitutes for a Lean type. The actual real interpretation and the full shared-world expression theorem remain E2.

**Theorem 1.1 (The exact quotient equals ordinary integer division on its domain).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.exactQuotient_eq_div`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.exactQuotient_eq_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain requires a nonzero divisor and divisibility. IntegerExactDivision.exactQuotient_unique and Int.ediv_mul_cancel identify the two quotients on that domain; one divided by two stays illegal.

**Theorem 1.2 (Readout commutes with every finite native expression).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.readout_eval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.readout_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constants use balancedSection and variables range over all BalancedRich d. The operations are complementBalanced, parallelBalanced, productBalanced and guarded exactDivide. The theorem includes both successful results and failure.

**Theorem 1.3 (Rich legality equals all ordinary node guards).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.legal_iff_all_nodes`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.legal_iff_all_nodes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic structural legality theorem retains both children and each nonzero-and-divisibility guard. This holds for every finite term and every assignment, in particular dimension three.

**Theorem 1.4 (Legal rich and ordinary results have equal values).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.value_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.value_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conditional value identity follows from full Option commutation. Ordinary evaluation itself remains partial at every division.

**Theorem 1.5 (Ordinary value equality is actual integer quotient equality).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.value_eq_iff_class_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.value_eq_iff_class_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IntegerQuotient.class_eq_iff identifies the result classes. This does not identify the raw archived histories.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.exactQuotient_eq_div`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.legal_iff_all_nodes`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.readout_eval`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.value_eq`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.value_eq_iff_class_eq`
- Dependency: [D5/S0/Rewriting/Expressions/GuardedArithmeticTerms](../../../S0/Rewriting/Expressions/GuardedArithmeticTerms.md)
- Dependency: [D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision](../SpacetimeArithmetic/IntegerExactDivision.md)
- Dependency: [D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient](../SpacetimeArithmetic/IntegerQuotient.md)
