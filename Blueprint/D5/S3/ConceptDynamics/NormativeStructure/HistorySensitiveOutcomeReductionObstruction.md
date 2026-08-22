# History-Sensitive Outcome Reduction Obstruction

## Abstract

Paths with one outcome and different evaluations obstruct outcome-only representation.

**Theorem 1.1 (History sensitivity obstructs outcome reduction).**

$$\forall Gamma, X, L: \operatorname{Type},\\{}e: Gamma \to X, J: Gamma \to L,\\{}{\exists gamma, gammaPrime: Gamma, e(gamma) = e(gammaPrime) \land J(gamma) \neq J(gammaPrime)} \Rightarrow\\{}\neg {\exists \overline{J}: X \to L, J = \operatorname{compose}(\overline{J}, e)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction.history_sensitive_evaluation_not_outcome_reducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path type, endpoint readout, and normative evaluation are independent source primitives on the canonical concept carrier.

History sensitivity is stated publicly by two paths with the same endpoint and different evaluations. Outcome reducibility is stated publicly as an endpoint function through which the evaluation factors.

The exact whole-codomain factorization criterion makes every represented evaluation constant on endpoint fibers. Applying it to the two witness paths contradicts their different evaluations.

The witness supplies an evaluation value, so the nonempty codomain needed by the exact extension theorem is derived rather than imposed as an additional source restriction.

No result function, endpoint, or evaluation is defined from the theorem's nonexistence target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction.history_sensitive_evaluation_not_outcome_reducible`
