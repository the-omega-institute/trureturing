# Two Sources of Path Dependence

## Abstract

Word order and transition incompatibility independently produce path dependence.

**Theorem 1.1 (Word order and gluing supply independent residuals).**

$$\begin{aligned}u: Bool \to \operatorname{Prod}\left(Unit, Bool\right) \to \operatorname{Prod}\left(Unit, Bool\right),\\\operatorname{apply}\left(u, a, \operatorname{pair}\left(star, b\right)\right) = \operatorname{pair}\left(star, \operatorname{if}\left(a, false, \operatorname{not}\left(b\right)\right)\right),\\\operatorname{Run}\left(u, \operatorname{word}\left(false, true\right), \operatorname{pair}\left(star, false\right)\right) \neq \operatorname{Run}\left(u, \operatorname{word}\left(true, false\right), \operatorname{pair}\left(star, false\right)\right),\\addFalse, addTrue: \operatorname{ClosureOperator}\left(\operatorname{Set}\left(Bool\right)\right), transition: \operatorname{OrderIso}\left(\operatorname{Set}\left(Bool\right), \operatorname{Set}\left(Bool\right)\right),\\\operatorname{apply}\left(addFalse, S\right) = \operatorname{union}\left(S, \operatorname{singleton}\left(false\right)\right), \operatorname{apply}\left(addTrue, S\right) = \operatorname{union}\left(S, \operatorname{singleton}\left(true\right)\right),\\\operatorname{apply}\left(transition, S\right) = \operatorname{image}\left(\operatorname{swap}\left(false, true\right), S\right),\\\operatorname{Commute}\left(addFalse, addTrue\right) \land \operatorname{apply}\left(transition, \operatorname{apply}\left(addFalse, empty\right)\right) \neq \operatorname{apply}\left(addFalse, \operatorname{apply}\left(transition, empty\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/PathDependenceSources.path_dependence_has_two_sources` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first witness uses one global product carrier Unit x Bool. Its two actions are applied by the canonical finite-word evaluator, and reversing the two-letter word changes the resulting state.

The second witness uses the powerset of Bool. Adding false and adding true are distinct bundled closure operators and commute locally. The Boolean swap induces a bijective order isomorphism on sets, but it does not intertwine the add-false closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/PathDependenceSources.path_dependence_has_two_sources`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../ObserverMemory/Prediction/ControlledBehaviorUniversality.md)
