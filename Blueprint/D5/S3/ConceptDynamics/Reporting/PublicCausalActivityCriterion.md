# Public Causal Activity Criterion and Separations

## Abstract

Public causal activity rules out public dynamic equivalence, while Boolean witnesses separate public activity, phenomenal difference, inertia, and static public equality.

**Lemma 1.1 (Public causal activity excludes dynamic equivalence).**

$$\forall State \in Type, Action \in Type, Public \in Type, intervene \in Action \to \left(State \to State\right), publicReadout \in \operatorname{Concept}\left(State, Public\right), x \in State, y \in State,\; \operatorname{PubliclyCausallyActive}\left(intervene, publicReadout, x, y\right) \Rightarrow \left(\neg \operatorname{PublicDynamicEquiv}\left(intervene, publicReadout, x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_causal_activity_excludes_dynamic_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A publicly active pair has an allowed action whose two resulting states receive different public values. Dynamic equivalence would require those values to agree after every allowed action.

The action witnessing activity therefore directly contradicts dynamic equivalence. The conclusion is one-way and does not assume that failure of a universal equality supplies a separating action.

**Lemma 1.2 (Public dynamic equivalence is public inertia).**

$$\forall State \in Type, Action \in Type, Public \in Type, intervene \in Action \to \left(State \to State\right), publicReadout \in \operatorname{Concept}\left(State, Public\right), x \in State, y \in State,\; \operatorname{PublicDynamicEquiv}\left(intervene, publicReadout, x, y\right) \Leftrightarrow \left(\forall m \in Action,\; publicReadout\left(intervene\left(m, x\right)\right) = publicReadout\left(intervene\left(m, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_dynamic_equiv_iff_inert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two states are dynamically equivalent exactly when every allowed action leaves their resulting public readouts equal. Thus the dynamic class records complete public inertia across the action family, rather than equality under only one chosen action.

**Lemma 1.3 (Public dynamic equivalence is an equivalence relation).**

$$\forall State \in Type, Action \in Type, Public \in Type, intervene \in Action \to \left(State \to State\right), publicReadout \in \operatorname{Concept}\left(State, Public\right),\; \operatorname{Equivalence}\left(\operatorname{PublicDynamicEquiv}\left(intervene, publicReadout\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_dynamic_equiv_is_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of public outcomes after every allowed action is reflexive and symmetric. If a first state agrees dynamically with a second and the second with a third, pointwise transitivity of equality makes the first and third dynamically equivalent.

Consequently the state space is partitioned into public dynamic classes for every intervention family and public readout.

**Lemma 1.4 (Phenomenal difference can coexist with public inertia).**

$$\operatorname{ZombieWitness}\left(zombiePhenomenal, zombiePublic\right) \land \left(\operatorname{PhenomenallyDifferent}\left(zombiePhenomenal, false, true\right) \land \left(\operatorname{PublicDynamicEquiv}\left(zombieIntervention, zombiePublic, false, true\right) \land \left(\neg \operatorname{PubliclyCausallyActive}\left(zombieIntervention, zombiePublic, false, true\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.phenomenal_difference_with_public_inertia` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the Boolean zombie pair, the phenomenal readout is the identity and therefore distinguishes false from true. Both coordinates of the joint public readout are constant, so the same pair is a zombie witness.

The only allowed intervention preserves the state. The constant public readout therefore remains equal on the pair after intervention, making the pair dynamically equivalent and not publicly active.

**Lemma 1.5 (Public activity can coexist with phenomenal agreement).**

$$\operatorname{PubliclyCausallyActive}\left(zombieIntervention, identityPublic, false, true\right) \land \left(constantPhenomenal\left(false\right) = constantPhenomenal\left(true\right) \land \left(\neg \operatorname{PhenomenallyDifferent}\left(constantPhenomenal, false, true\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_activity_with_phenomenal_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the identity public readout and the identity intervention, false and true produce different public values and hence form a publicly active pair.

A constant phenomenal readout assigns false to both states. Their phenomenal values agree, so public causal activity does not by itself imply phenomenal difference.

**Lemma 1.6 (Static public equality can hide dynamic separation).**

$$hiddenBitPublic\left(\operatorname{pair}\left(false, false\right)\right) = hiddenBitPublic\left(\operatorname{pair}\left(false, true\right)\right) \land \left(\operatorname{PubliclyCausallyActive}\left(revealHiddenBit, hiddenBitPublic, \operatorname{pair}\left(false, false\right), \operatorname{pair}\left(false, true\right)\right) \land \left(\neg \operatorname{PublicDynamicEquiv}\left(revealHiddenBit, hiddenBitPublic, \operatorname{pair}\left(false, false\right), \operatorname{pair}\left(false, true\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.static_public_equality_with_dynamic_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two private Boolean pairs have the same first bit, so the static public readout cannot distinguish them. They differ only in the second, initially hidden bit.

The revealing intervention copies that hidden bit into the public first coordinate. Their resulting public values then differ, making the pair publicly active and dynamically inequivalent despite its static public equality.

**Theorem 1.7 (The public causal activity criterion and all separations hold together).**

$$\left(\forall State \in Type, Action \in Type, Public \in Type, intervene \in Action \to \left(State \to State\right), publicReadout \in \operatorname{Concept}\left(State, Public\right), x \in State, y \in State,\; \operatorname{PubliclyCausallyActive}\left(intervene, publicReadout, x, y\right) \Rightarrow \left(\neg \operatorname{PublicDynamicEquiv}\left(intervene, publicReadout, x, y\right)\right)\right) \land \left(\left(\forall State \in Type, Action \in Type, Public \in Type, intervene \in Action \to \left(State \to State\right), publicReadout \in \operatorname{Concept}\left(State, Public\right), x \in State, y \in State,\; \operatorname{PublicDynamicEquiv}\left(intervene, publicReadout, x, y\right) \Leftrightarrow \left(\forall m \in Action,\; publicReadout\left(intervene\left(m, x\right)\right) = publicReadout\left(intervene\left(m, y\right)\right)\right)\right) \land \left(\operatorname{Equivalence}\left(\operatorname{PublicDynamicEquiv}\left(zombieIntervention, zombiePublic\right)\right) \land \left(\left(\operatorname{ZombieWitness}\left(zombiePhenomenal, zombiePublic\right) \land \left(\operatorname{PhenomenallyDifferent}\left(zombiePhenomenal, false, true\right) \land \left(\operatorname{PublicDynamicEquiv}\left(zombieIntervention, zombiePublic, false, true\right) \land \left(\neg \operatorname{PubliclyCausallyActive}\left(zombieIntervention, zombiePublic, false, true\right)\right)\right)\right)\right) \land \left(\left(\operatorname{PubliclyCausallyActive}\left(zombieIntervention, identityPublic, false, true\right) \land \left(constantPhenomenal\left(false\right) = constantPhenomenal\left(true\right) \land \left(\neg \operatorname{PhenomenallyDifferent}\left(constantPhenomenal, false, true\right)\right)\right)\right) \land \left(hiddenBitPublic\left(\operatorname{pair}\left(false, false\right)\right) = hiddenBitPublic\left(\operatorname{pair}\left(false, true\right)\right) \land \left(\operatorname{PubliclyCausallyActive}\left(revealHiddenBit, hiddenBitPublic, \operatorname{pair}\left(false, false\right), \operatorname{pair}\left(false, true\right)\right) \land \left(\neg \operatorname{PublicDynamicEquiv}\left(revealHiddenBit, hiddenBitPublic, \operatorname{pair}\left(false, false\right), \operatorname{pair}\left(false, true\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_causal_activity_criterion_and_separations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The criterion combines the general obstruction from public activity, the pointwise characterization of dynamic inertia, and the equivalence-relation structure of the Boolean zombie dynamics.

Its three concrete witnesses then separate the relevant notions in both directions: phenomenal difference can be publicly inert, public activity can leave phenomenal values equal, and static public equality can be broken only after intervention.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.phenomenal_difference_with_public_inertia`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_activity_with_phenomenal_agreement`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_causal_activity_criterion_and_separations`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_causal_activity_excludes_dynamic_equivalence`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_dynamic_equiv_iff_inert`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.public_dynamic_equiv_is_equivalence`
- Truth anchor: `D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.static_public_equality_with_dynamic_separation`
- Dependency: [D5/S3/ConceptDynamics/Reporting/PhenomenalSupervenience](PhenomenalSupervenience.md)
