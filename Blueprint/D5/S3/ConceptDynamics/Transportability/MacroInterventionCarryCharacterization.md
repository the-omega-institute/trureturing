# Macro-Intervention Carry Characterization

## Abstract

Intervention carry characterizes effective-image macro descent.

**Theorem 1.1 (Carry emptiness and macro-intervention existence constrain each other).**

$$\begin{gathered}\forall X, Z: \operatorname{Type},\\{}F: X \to X, C: X \to Z,\\{}((\exists G: Z \to Z, \operatorname{MacroIntervention}(F, C, C, G)) \Rightarrow \operatorname{IsEmpty}(\operatorname{Carry}(F, C, C))) \land\\{}(\operatorname{IsEmpty}(\operatorname{Carry}(F, C, C)) \Rightarrow \exists! Gbar: \operatorname{range}(C) \to Z, \operatorname{EffectiveImageDescent}(F, C, C, Gbar)) \land\\{}(\forall kappa: \operatorname{Carry}(F, C, C), \neg(\exists G: Z \to Z, \operatorname{MacroIntervention}(F, C, C, G))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transportability/MacroInterventionCarryCharacterization.macro_intervention_carry_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a micro-level intervention on X and let C map micro states to the macro carrier Z. The imported family primitives define ambient commutation, intervention carry, and descent on range(C).

The forward clause needs only an ambient commuting intervention. The reverse clause independently needs only empty carry and constructs a unique map on the realized image, without a finiteness premise.

The final public clause takes an actual carry inhabitant and rules out every ambient commuting intervention, exposing the source theorem's nonexistence-witness interpretation directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transportability/MacroInterventionCarryCharacterization.macro_intervention_carry_characterization`
- Dependency: [D5/S3/ConceptDynamics/Transport/MacroInterventionCriterion](../Transport/MacroInterventionCriterion.md)
