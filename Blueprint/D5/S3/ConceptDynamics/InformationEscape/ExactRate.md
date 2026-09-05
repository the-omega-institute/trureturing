# Exact Escape Rates

## Abstract

Exact finite counts turn escape reduction into positive unique capture.

**Definition 1.1 (Escape denominator).**

$$\operatorname{escapeDenominator}(A) = \operatorname{card}(\operatorname{offDiagonalPairs}(\operatorname{State}(A))).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite arena and catalog kernels.

**Theorem 1.2 (Ordered-pair denominator formula).**

$$\operatorname{escapeDenominator}(A) = \operatorname{card}(A) \times (\operatorname{card}(A) - 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeDenominator_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses exact Finset cardinality and rational order transport.

**Theorem 1.3 (Nondegenerate denominator is positive).**

$$\operatorname{Nondegenerate}(A) \Rightarrow 0 < \operatorname{escapeDenominator}(A).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeDenominator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses exact Finset cardinality and rational order transport.

**Definition 1.4 (Escape numerator).**

$$\operatorname{escapeNumerator}(C, S) = \operatorname{card}(\operatorname{escapePairs}(C, S)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite arena and catalog kernels.

**Definition 1.5 (Exact escape rate).**

$$\operatorname{escapeRate}(C, S) = \frac{\operatorname{escapeNumerator}(C, S)}{\operatorname{escapeDenominator}(A)}.$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite arena and catalog kernels.

**Definition 1.6 (Unique capture count).**

$$\operatorname{uniqueCaptureCount}(C, i) = \operatorname{card}(\operatorname{uniqueCapturePairs}(C, i)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExactRate.uniqueCaptureCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite arena and catalog kernels.

**Definition 1.7 (Theorem gain rate).**

$$\operatorname{theoremGainRate}(C, i) = \frac{\operatorname{uniqueCaptureCount}(C, i)}{\operatorname{escapeDenominator}(A)}.$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExactRate.theoremGainRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite arena and catalog kernels.

**Definition 1.8 (Strictly lowers escape).**

$$\operatorname{LowersEscape}(C, i) \Leftrightarrow \operatorname{escapeRate}(C, \operatorname{fullIndexSet}(C)) < \operatorname{escapeRate}(C, \operatorname{without}(C, i)).$$

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ExactRate.LowersEscape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition is computed from the finite arena and catalog kernels.

**Theorem 1.9 (Leave-one-out numerator decomposition).**

$$\operatorname{escapeNumerator}(C, \operatorname{without}(C, i)) = \operatorname{escapeNumerator}(C, \operatorname{fullIndexSet}(C)) + \operatorname{uniqueCaptureCount}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeNumerator_without_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses exact Finset cardinality and rational order transport.

**Theorem 1.10 (Rate difference equals gain).**

$$\operatorname{Nondegenerate}(A) \Rightarrow \operatorname{escapeRate}(C, \operatorname{without}(C, i)) - \operatorname{escapeRate}(C, \operatorname{fullIndexSet}(C)) = \operatorname{theoremGainRate}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExactRate.theoremGainRate_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses exact Finset cardinality and rational order transport.

**Theorem 1.11 (Strict reduction criterion).**

$$\operatorname{Nondegenerate}(A) \Rightarrow \operatorname{LowersEscape}(C, i) \Leftrightarrow 0 < \operatorname{uniqueCaptureCount}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExactRate.lowersEscape_iff_uniqueCaptureCount_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses exact Finset cardinality and rational order transport.

**Theorem 1.12 (Unique capture witness criterion).**

$$0 < \operatorname{uniqueCaptureCount}(C, i) \Leftrightarrow \exists x, y, x \neq y \land (\forall j, j \neq i \Rightarrow \operatorname{agrees}(\operatorname{theoremAt}(C, j), x, y)) \land \neg\operatorname{agrees}(\operatorname{theoremAt}(C, i), x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/ExactRate.uniqueCaptureCount_pos_iff_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses exact Finset cardinality and rational order transport.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.LowersEscape`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeDenominator`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeDenominator_eq`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeDenominator_pos`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeNumerator`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeNumerator_without_eq`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.escapeRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.lowersEscape_iff_uniqueCaptureCount_pos`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.theoremGainRate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.theoremGainRate_eq`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.uniqueCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ExactRate.uniqueCaptureCount_pos_iff_witness`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/EscapePairs](EscapePairs.md)
