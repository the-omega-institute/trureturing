# Descriptive Announcement Commutation

## Abstract

Conditioning by two descriptive announcements commutes.

**Theorem 1.1 (Descriptive announcements commute).**

$$\forall X: \operatorname{Type}, P, Q: \operatorname{Set}\left(X\right),\\{}\operatorname{descriptiveCondition}\left(P\right) \circ \operatorname{descriptiveCondition}\left(Q\right) = \operatorname{descriptiveCondition}\left(Q\right) \circ \operatorname{descriptiveCondition}\left(P\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation.descriptive_announcement_commutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A descriptive announcement is the canonical operation that intersects the currently admitted states with the announcement predicate.

For arbitrary state types and announcement predicates, composing the two conditioning operators in either order gives the same operator.

The proof unfolds the conditioning semantics and directly applies the pinned-library identity Set.inter_right_comm. Repository searches found no pre-existing descriptive-announcement primitive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation.descriptive_announcement_commutation`
