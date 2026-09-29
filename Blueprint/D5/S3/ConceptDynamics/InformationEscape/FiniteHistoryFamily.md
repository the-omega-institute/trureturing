# FiniteHistoryFamily

## Abstract

The finite-history consumer retains the full dependent probability law across all history lengths.

**Definition 1.1 (All history fibers).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.signature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parameters are triples (J, Z, N) with J : Type u, Z : Nat → Type v and N : Nat. States are J × History Z N, the sole Unit role outputs History Z N, and anchors are Empty. The family retains both universes and every N, including zero; finiteness of each history does not make the family domain finite.

**Definition 1.2 (Three conjuncts on the original measure).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.Law`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.Law` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law retains the probability-measure assertion for historyLaw ν K N, the integral-to-finite-sum identity for every t ≤ N and test function, and the almost-everywhere conditional-expectation identity for every t < N. All nonnegativity and normalization premises for ν and K remain. The readout replaces the history projection in the integral, conditioning and posterior expression while the original measure remains fixed.

**Definition 1.3 (Readout-induced conditioning).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.readoutSigma`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.readoutSigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditioning sigma-algebra is the comap of the t-prefix of the observed history. At the identity readout it is the source history filtration; changing observations must also change this conditioning object, not just the integrand.

**Definition 1.4 (Complete thirteen-binder statement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.FullLaw`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.FullLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FullLaw quantifies J and Z, the six Fintype/MeasurableSpace/MeasurableSingletonClass dictionaries (including their dependent families), and ν, hν, K, N, hK: thirteen binders in the source order, with universes u and v retained. No positive-length restriction is added. At N = 0 the t < N clause has no instances, while the other two conjuncts remain.

**Definition 1.5 (Actual history observation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.actual`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.actual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual sole readout returns the history component of the state. The arena applies FullLaw to this complete readout family, not to a chosen distribution or a finite sample of histories.

**Definition 1.6 (One-fiber intervention).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.rejected`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.rejected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

badFiber changes only (ULift Unit, the constant ULift Bool family, 1), returning the always-true history there and the original history elsewhere. targetNu is unit mass, targetK always emits false, and targetF detects true. These operands support the law-breaking witness without restricting FullLaw to that fiber.

The preserved source is `D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation.history_law_conditional_expectation`. Its Reg mirror supplies the definitional bridge and uses Reg/Support/FiniteHistoryFamily for variation, sensitivity and actual observational dependence. Source coordinates retain J, Z and N, with the complete statement and dictionaries reconstructed by source binding.

This is repository-derived consumer-model content, not a new theorem wrapper or a coverage, novelty or freeze claim. The original theorem and Reg proofs remain the authority for their respective obligations. The registration's raw open residual means unknown residual information, not infinity, undecidability or completeness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.FullLaw`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.Law`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.actual`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.readoutSigma`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.rejected`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily.signature`
- Truth anchor: `D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation.history_law_conditional_expectation`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
- Dependency: [D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation](../../Estimation/DataProcessing/FiniteHistoryConditionalExpectation.md)
