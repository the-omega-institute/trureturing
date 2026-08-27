# Cocycle And Policy Separation

## Abstract

Cocycle accounting does not determine which legal action a policy selects.

**Theorem 1.1 (Cocycle composition leaves policy choice nonunique).**

$$\forall U, Sigma, Case, PublicFact, Outcome: \operatorname{Type}, [\operatorname{Nonempty}\left(U\right)], [\operatorname{AddCommGroup}\left(Sigma\right)], projection: \operatorname{AddMonoidHom}\left(Sigma, \operatorname{AddCircle}\left(1\right)\right), hProjectionSurjective: \operatorname{Surjective}\left(projection\right), hiddenEquiv: \operatorname{AdditiveEquiv}\left(HiddenJumpCoordinates, \operatorname{ker}\left(projection\right)\right), sectionAlpha, sectionBeta, sectionGamma: U \to Sigma, jumpAlphaBeta, jumpBetaGamma, jumpAlphaGamma: U \to HiddenJumpCoordinates, hAlphaBeta: \forall u, sectionBeta(u) = sectionAlpha(u) + hiddenEquiv(jumpAlphaBeta(u)), hBetaGamma: \forall u, sectionGamma(u) = sectionBeta(u) + hiddenEquiv(jumpBetaGamma(u)), publicLaw: Case \to PublicFact, admissible: Case \to \operatorname{Prop}, permitted: Case \to Outcome \to \operatorname{Prop}, b: PublicFact, \exists leftOutcome, rightOutcome: Outcome, leftOutcome \neq rightOutcome \land (\exists x: Case, admissible(x) \land publicLaw(x) = b \land permitted(x)(leftOutcome)) \land \exists x: Case, admissible(x) \land publicLaw(x) = b \land permitted(x)(rightOutcome) \Rightarrow ((\forall u, projection(sectionAlpha(u)) = projection(sectionBeta(u)) \land projection(sectionBeta(u)) = projection(sectionGamma(u))) \land (\forall u, sectionGamma(u) = sectionAlpha(u) + hiddenEquiv(jumpAlphaGamma(u)) \iff \forall u, jumpAlphaGamma(u) = jumpAlphaBeta(u) + jumpBetaGamma(u)) \land (\exists u, jumpAlphaGamma(u) \neq jumpAlphaBeta(u) + jumpBetaGamma(u) \Rightarrow \exists u, sectionGamma(u) \neq sectionAlpha(u) + hiddenEquiv(jumpAlphaGamma(u)))) \land \neg(\exists! candidate: Outcome, \exists x: Case, admissible(x) \land publicLaw(x) = b \land permitted(x)(candidate)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/CocyclePolicySeparation.cocycle_does_not_select_policy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden-jump construction records visible agreement, the endpoint/cocycle equivalence, and an explicit endpoint residual when the selected jumps disagree.

The same public model carries a permitted-outcome relation with two distinct outcomes in one public-law fiber. Consequently the cocycle law supplies composition and accounting, but no unique policy choice.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/CocyclePolicySeparation.cocycle_does_not_select_policy`
- Dependency: [D5/S1/Dynamics/JumpCocycle](../../../S1/Dynamics/JumpCocycle.md)
- Dependency: [D5/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness](DiscretionaryOutcomeNonuniqueness.md)
