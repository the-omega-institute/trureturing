# Explainable but Not Contestable

## Abstract

A public rule can remain explainable while case and appeal evidence cannot determine its outcome.

**Theorem 1.1 (A public rule need not make its outcome contestable).**

$$\begin{gathered}\exists q_{R}, q_{L}, q_{C}, q_{A}: Bool \times Bool \to Bool, T: Bool \times Bool \to Bool,\\{}\operatorname{Refines}\left(q_{R}, q_{L}\right) \land (\forall x, y: Bool \times Bool, q_{A}(x) = q_{A}(y)) \land\\{}\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{conceptJoin}\left(q_{C}, q_{A}\right)\right) \land\\{}\exists x, y: Bool \times Bool, T(x) \neq T(y) \land \operatorname{conceptJoin}\left(q_{C}, q_{A}\right)(x) = \operatorname{conceptJoin}\left(q_{C}, q_{A}\right)(y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Appeal/ExplainableNotContestable.explainable_not_contestable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the state space to be two Boolean coordinates. The rule, its public language, and the case record all reveal the first coordinate, so the rule is fully explainable through the public language.

The appeal readout is constant and therefore contributes no new distinction. The classification target is the second coordinate, which the joined case-and-appeal evidence does not reveal.

In particular, the states (false, false) and (false, true) have the same case record and the same appeal evidence, but their target outcomes differ. Hence no function of the available joined evidence can recover the canonical target readout.

This finite witness separates publication of the governing rule from contestability of an individual outcome: knowing the rule does not supply the case-specific coordinate needed to challenge the classification.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Appeal/ExplainableNotContestable.explainable_not_contestable`
- Dependency: [D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence](../Interventions/RedundantAppealDefectPersistence.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
