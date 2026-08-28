# Intervention Image Defect

## Abstract

A family of intervention laws outside a model class's realizable image cannot be explained by one model across every regime.

**Theorem 1.1 (Image defect excludes a joint explaining model).**

$$\forall Model \in \operatorname{Type}\left(\right), Regime \in \operatorname{Type}\left(\right), Law \in \operatorname{Type}\left(\right), modelClass \in \operatorname{Set}\left(Model\right), interventionLaw \in Model \to \left(Regime \to Law\right), observedLaw \in Regime \to Law,\; \left(\neg observedLaw \in \left\{(\lambda regime, interventionLaw\left(model, regime\right)) \mid model \in modelClass\right\}\right) \Rightarrow \left(\neg \left(\exists model \in Model,\; model \in modelClass \land \left(\forall regime \in Regime,\; interventionLaw\left(model, regime\right) = observedLaw\left(regime\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/InterventionImageDefect.image_defect_excludes_joint_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model class is a subset of an ambient model carrier. Each model is sent to its complete family of laws indexed by intervention regimes.

Image defect says that the observed family is not one of those restricted intervention profiles. A model explaining every regime would construct exactly such a profile, contradicting the defect.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/InterventionImageDefect.image_defect_excludes_joint_model`
