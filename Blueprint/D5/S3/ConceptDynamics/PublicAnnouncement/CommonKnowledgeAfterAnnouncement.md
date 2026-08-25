# Common Knowledge After Public Announcement

## Abstract

A true public announcement makes its announced proposition common knowledge.

**Theorem 1.1 (True public announcements create common knowledge).**

$$\forall State, Agent: Type, access: Agent \to \left(State \to \left(State \to Prop\right)\right), P: State \to Prop, a: State,\\{}\operatorname{P}\left(a\right) \Rightarrow\\{}\exists aPrime \in \operatorname{announcedModel}\left(P\right),\; \operatorname{fst}\left(aPrime\right) = a \land \left(\forall x \in \operatorname{announcedModel}\left(P\right),\; \operatorname{ReflTransGen}\left(\operatorname{announcementStep}\left(access\right), aPrime, x\right) \Rightarrow \operatorname{P}\left(\operatorname{fst}\left(x\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PublicAnnouncement/CommonKnowledgeAfterAnnouncement.true_public_announcement_is_common_knowledge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is built by applying the repository's canonical descriptive announcement restriction to the universal model.

An arbitrary agent accessibility relation is retained on the announced subtype, and common knowledge is the proposition at every state in the reflexive-transitive finite path closure from the actual anchor.

Because every post-announcement representative carries the public predicate as its subtype evidence, every iterated information path satisfies that predicate. Repository searches found no exact packaged public-announcement/common-knowledge theorem; Mathlib's Relation.ReflTransGen is applied for path closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PublicAnnouncement/CommonKnowledgeAfterAnnouncement.true_public_announcement_is_common_knowledge`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation](../Epistemic/DescriptiveAnnouncementCommutation.md)
