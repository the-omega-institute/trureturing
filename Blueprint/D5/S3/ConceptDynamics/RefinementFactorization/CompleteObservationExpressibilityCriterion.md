# Complete Observation Expressibility Criterion

## Abstract

A target is expressible from the complete observation exactly when it is constant on every joint fiber.

**Theorem 1.1 (Expressibility, kernel inclusion, and fiber constancy agree).**

$$\begin{gathered}\forall I, X, Y: \operatorname{Type},\\{}V: I \to \operatorname{Type}, q: \forall i: I, X \to V(i),\\{}T: X \to Y,\\{}\operatorname{ListTFAE}({[\operatorname{Refines}(T, \operatorname{effectiveReadout}(\operatorname{jointReadout}(q))), \operatorname{ker}(\operatorname{jointReadout}(q)) \subseteq \operatorname{ker}(T), \forall x, y: X, (\forall i: I, q(i)(x) = q(i)(y)) \Rightarrow T(x) = T(y)]}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/CompleteObservationExpressibilityCriterion.complete_observation_expressibility_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The indexed observations are assembled by the canonical dependent joint readout and normalized to their realized image.

The displayed theorem retains all three source clauses: effective-image factorization, equality-kernel inclusion, and the componentwise fiber implication.

The reverse implication constructs the factor only on realized profiles using the pinned range splitting operation, so no values are chosen for unrealized profiles.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/CompleteObservationExpressibilityCriterion.complete_observation_expressibility_tfae`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality](../DefinitionEscape/QuestionAlgebraDuality.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
