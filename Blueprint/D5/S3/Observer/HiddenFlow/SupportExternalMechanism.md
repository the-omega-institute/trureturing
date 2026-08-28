# Support-External Mechanism

## Abstract

A mechanism value outside an accessed support can change without changing the observed channel.

**Theorem 1.1 (An unseen parent configuration is not identified by the observed channel).**

$$\forall Parent \in \operatorname{Type}, Outcome \in \operatorname{Type}, support \in \operatorname{Set}\left(Parent\right), hidden \in Parent,\; \left(\operatorname{Nontrivial}\left(Outcome\right) \land \left(\neg support\left(hidden\right)\right)\right) \Rightarrow \left(\exists mechanism0 \in Parent \to Outcome, mechanism1 \in Parent \to Outcome,\; observationChannel\left(support\right)\left(mechanism0\right) = observationChannel\left(support\right)\left(mechanism1\right) \land mechanism0\left(hidden\right) \ne mechanism1\left(hidden\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/SupportExternalMechanism.unseen_parent_config_can_change_without_observed_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support predicate is the set of parent configurations accessed by the behavior regime. The observation channel is the canonical restriction of a structural mechanism to that support.

When a hidden configuration lies outside the support, two mechanisms can agree on every accessed parent and still take distinct values at the hidden parent. The Boolean corollary supplies a concrete nontrivial model.

The theorem exposes both source clauses publicly: equality of observed channels and inequality of the hidden mechanism values.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/SupportExternalMechanism.unseen_parent_config_can_change_without_observed_law`
