# Common Knowledge on an Admissible Announcement Domain

## Abstract

A true public announcement creates common knowledge on the restricted admitted domain.

**Theorem 1.1 (True public announcements create common knowledge).**

$$\begin{aligned}\forall State, Agent: Type,\\A, P: \operatorname{Set}\left(State\right), access: Agent \to \left(State \to \left(State \to Prop\right)\right), a: State,\\a\in A \land a\in P \Rightarrow\\\exists aPrime: \operatorname{Subtype}\left(\operatorname{descriptiveCondition}\left(P, A\right)\right), \operatorname{fst}\left(aPrime\right) = a \land \\\forall t: \operatorname{Subtype}\left(\operatorname{descriptiveCondition}\left(P, A\right)\right), \operatorname{ReflTransGen}\left((\lambda s, t \mapsto \exists i: Agent, \operatorname{access}\left(i, \operatorname{fst}\left(s\right), \operatorname{fst}\left(t\right)\right)), aPrime, t\right) \Rightarrow \operatorname{fst}\left(t\right)\in P.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PublicAnnouncement/AdmissibleAnnouncementCommonKnowledge.true_public_announcement_is_common_knowledge_on_admitted_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pre-announcement admitted domain A and public proposition P are both public inputs. The post-announcement carrier is constructed by the canonical descriptiveCondition(P,A) restriction.

Common reachability is the reflexive-transitive closure of steps witnessed by one agent's accessibility relation. Every target in the restricted carrier satisfies P by its membership evidence.

The actual anchor is required to lie in A and P, so it embeds into the post-announcement carrier without replacing A by the universal set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PublicAnnouncement/AdmissibleAnnouncementCommonKnowledge.true_public_announcement_is_common_knowledge_on_admitted_domain`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation](../Epistemic/DescriptiveAnnouncementCommutation.md)
