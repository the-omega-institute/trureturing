# Macro-Intervention Carry Criterion

## Abstract

Macro interventions are characterized by empty carry.

**Theorem 1.1 (Existence excludes carry; empty carry gives unique descent).**

$$\forall X, Y, B_{C}, B_{D}: \operatorname{Type},\ [\operatorname{Fintype}(X)], [\operatorname{DecidableEq}(X)], [\operatorname{Fintype}(B_{C})], [\operatorname{DecidableEq}(B_{C})], [\operatorname{Fintype}(B_{D})], [\operatorname{DecidableEq}(B_{D})],\ F: X \to Y, C: X \to B_{C}, D: Y \to B_{D},\ {((\exists G: B_{C} \to B_{D}, \operatorname{MacroIntervention}(F, C, D, G)) \Rightarrow \operatorname{IsEmpty}(\operatorname{Carry}(F, C, D)))} \land {(\operatorname{IsEmpty}(\operatorname{Carry}(F, C, D)) \Rightarrow \exists! \overline{G}: \operatorname{range}(C) \to B_{D}, \operatorname{EffectiveImageDescent}(F, C, D, \overline{G}))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/MacroInterventionCriterion.macro_intervention_carry_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a process, let C be its current readout, and let D be the future readout. A macro intervention G on the ambient readout codomain commutes when G(C(x)) equals D(F(x)) for every source state x.

If such an ambient intervention exists, two states identified by C cannot be separated by D after F, so the intervention-carry type is empty. Conversely, in the finite decidable model, empty carry determines a unique intervention on the effective image range(C). The reverse implication directly reuses the repository theorem FiniteReverseCriterion.

The two directions deliberately have different domains: the forward hypothesis supplies G on the full readout codomain, while the reverse conclusion asserts uniqueness only on the realized effective image. No extension outside that image is claimed.

This formalizes theorem/510.1 of formal-concept-dynamics, atom generic-residual-11d26e8120ab721779698193df66228d9ce5276b1c732982aaeee841a3f83ee2.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/MacroInterventionCriterion.macro_intervention_carry_criterion`
- Dependency: [D5/S3/ConceptDynamics/Transport/FiniteReverseCriterion](FiniteReverseCriterion.md)
