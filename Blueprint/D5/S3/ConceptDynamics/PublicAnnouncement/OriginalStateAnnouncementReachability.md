# Public Announcement on the Original State Carrier

## Abstract

A true announcement is preserved along every restricted access path.

**Theorem 1.1 (True public announcements create common knowledge).**

$$\forall State, Agent: Type, access: Agent \to \left(State \to \left(State \to Prop\right)\right),\\{}P: State \to Prop, a: State,\\{}\operatorname{P}\left(a\right) \Rightarrow\\{}\forall t \in State,\; \operatorname{ReflTransGen}\left((\lambda s, t \mapsto \operatorname{P}\left(s\right) \land \operatorname{P}\left(t\right) \land \exists i: Agent, \operatorname{access}\left(i, s, t\right)), a, t\right) \Rightarrow \operatorname{P}\left(t\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PublicAnnouncement/OriginalStateAnnouncementReachability.true_public_announcement_is_common_knowledge_on_original_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The post-announcement accessibility relation is displayed directly: both endpoints satisfy the public predicate and some agent relates the source endpoint to the target endpoint.

The state carrier remains the original State type. The actual anchor's truth is a public premise, and common knowledge quantifies over every state in the reflexive-transitive closure of the restricted relation.

The proof inducts on the supplied ReflTransGen path. The reflexive case uses the true-anchor premise, while a nontrivial final step carries the target predicate as part of the announcement restriction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PublicAnnouncement/OriginalStateAnnouncementReachability.true_public_announcement_is_common_knowledge_on_original_states`
