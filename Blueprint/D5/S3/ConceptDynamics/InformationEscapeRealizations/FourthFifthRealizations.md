# Fourth and Fifth Legacy Primitive Realizations

## Abstract

Two frozen statements are equivalent to contextual and causal realization laws.

**Definition 1.1 (Context realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.contextRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.contextRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed realization reads every context field, decides both fixed-meaning predicates, and anchors the baseline and alternate contexts.

**Theorem 1.2 (Context-selected fixed meanings certificate).**

$$((baselineContext.text = alternateContext.text) \land (baselineContext.interpretationRule = alternateContext.interpretationRule) \land (baselineContext.readerAdmission \neq alternateContext.readerAdmission) \land (baselineContext.background \neq alternateContext.background) \land (baselineContext.evaluationGoal \neq alternateContext.evaluationGoal) \land (\operatorname{IsBinaryFixedMeaning}(baselineContext, (false, false, false))) \land (\operatorname{IsBinaryFixedMeaning}(alternateContext, (true, true, true))) \land ((false, false, false) \neq (true, true, true))) \iff contextArena.Law contextRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.context_parameters_can_select_distinct_fixed_points_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate identifies every clause of the frozen context proposition with contextArena.Law contextRealization.

**Definition 1.3 (Intervention realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.interventionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.interventionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed realization uses Int and CF as its intervention and counterfactual readouts and has no point anchors.

**Theorem 1.4 (Intervention is weaker than counterfactual certificate).**

$$(\exists M N: DeterministicBoolSCM, (\operatorname{Int}(M) = \operatorname{Int}(N)) \land (\operatorname{CF}(M) \neq \operatorname{CF}(N))) \iff interventionArena.Law interventionRealization.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.intervention_strictly_weaker_than_counterfactual_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate identifies the frozen existential Int-versus-CF separation with interventionArena.Law interventionRealization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.contextRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.context_parameters_can_select_distinct_fixed_points_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.interventionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.intervention_strictly_weaker_than_counterfactual_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas](../InformationEscapeArenas/FourthFifthArenas.md)
