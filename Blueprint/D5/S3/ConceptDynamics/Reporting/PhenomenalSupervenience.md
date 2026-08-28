# Phenomenal Supervenience and Zombie Witnesses

## Abstract

Phenomenal factorization through a selected joint public readout is exactly the absence of a zombie witness, with Boolean choices realizing both outcomes.

**Theorem 1.1 (Phenomenal supervenience is equivalent to having no zombie witness).**

$$\left(\forall X \in Type, Phenomenal \in Type, PublicLeft \in Type, PublicRight \in Type, p \in X \to Phenomenal, qL \in X \to PublicLeft, qR \in X \to PublicRight,\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\operatorname{Refines}\left(p, \operatorname{conceptJoin}\left(qL, qR\right)\right) \Leftrightarrow \left(\neg \operatorname{ZombieWitness}\left(p, \operatorname{conceptJoin}\left(qL, qR\right)\right)\right)\right)\right) \land \left(\operatorname{ZombieWitness}\left(\operatorname{identity}\left(Bool\right), \operatorname{conceptJoin}\left(\operatorname{constant}\left(false\right), \operatorname{constant}\left(false\right)\right)\right) \land \left(\neg \operatorname{ZombieWitness}\left(\operatorname{identity}\left(Bool\right), \operatorname{conceptJoin}\left(\operatorname{identity}\left(Bool\right), \operatorname{constant}\left(false\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PhenomenalSupervenience.supervenience_xor_zombie_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any inhabited state space, a phenomenal readout factors through the joint value of two selected public readouts exactly when it is constant on every joint-public fiber. Equivalently, no two publicly indistinguishable states differ phenomenally.

For the first Boolean instance, both public coordinates are constantly false. The states false and true therefore have the same joint public value, while the identity phenomenal readout distinguishes them, producing a zombie witness.

For the second Boolean instance, the first public coordinate is the identity. Equality of joint public values then forces equality of the states, so the identity phenomenal readout cannot differ. Changing only the selected public concept removes the witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PhenomenalSupervenience.supervenience_xor_zombie_witness`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
