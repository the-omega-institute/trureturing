# Correctness and Path Legitimacy

## Abstract

Equal correct results cannot determine opposite path legitimacy.

**Theorem 1.1 (A correct result does not determine path legitimacy).**

$$\forall Gamma, R,\\{}r: Gamma \to R, C, L: Gamma \to Prop,\\{}gamma_{a}, gamma_{u}\in Gamma,\\{}r(gamma_{a}) = r(gamma_{u}) \land C(gamma_{a}) \land C(gamma_{u}) \land L(gamma_{a}) \land \neg L(gamma_{u}) \Rightarrow\\{}\neg \exists D: R \to Prop, \forall gamma\in Gamma, C(gamma) \Rightarrow (D(r(gamma)) \iff L(gamma)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/CorrectnessLegitimacySeparation.correct_result_does_not_determine_legitimacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two paths that reach the same result and satisfy the same correctness predicate. The first path is legitimate and the second is not.

Any proposed predicate of results must assign the same proposition to both paths because their results are equal. Agreement with legitimacy on all correct paths would therefore both accept and reject that common result, which is impossible.

The path predicates and result map are independent inputs, so legitimacy is not defined from the desired non-determination conclusion. The proof directly applies equality transport from the pinned library.

Repository and pinned-library searches found no exact theorem combining equal correct results, opposite path legitimacy, and result-only decision failure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/CorrectnessLegitimacySeparation.correct_result_does_not_determine_legitimacy`
- Dependency: [D5/S3/ConceptDynamics/LegitimacyCorrectness](../LegitimacyCorrectness.md)
