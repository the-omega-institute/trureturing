# Prediction and Decision Sufficiency Strictness

## Abstract

Prediction determines losses and actions, but actions need not determine prediction.

**Theorem 1.1 (Prediction sufficiency implies decision sufficiency strictly).**

$$\forall X \in Type, C \in Type, Outcome \in Type, Action \in Type,\; \left(\operatorname{MeasurableSpace}\left(Outcome\right) \land \operatorname{MeasurableSingletonClass}\left(Outcome\right)\right) \Rightarrow \left(\forall prediction \in X \to \operatorname{PMF}\left(Outcome\right), concept \in X \to C, loss \in Action \to \left(Outcome \to \mathbb{R}\right),\; \operatorname{let} expectedLoss: X \to \left(Action \to \mathbb{R}\right), \forall state \in X, action \in Action,\; expectedLoss\left(state, action\right) = \operatorname{integral}\left(\operatorname{toMeasure}\left(prediction\left(state\right)\right), loss\left(action\right)\right); \operatorname{let} optimalActions: X \to \operatorname{Set}\left(Action\right), \forall state \in X,\; optimalActions\left(state\right) = \left\{action: Action \mid \forall alternative \in Action,\; expectedLoss\left(state, action\right) \le expectedLoss\left(state, alternative\right)\right\}; \left(\operatorname{Refines}\left(prediction, concept\right) \Rightarrow \left(\operatorname{Refines}\left(expectedLoss, concept\right) \land \operatorname{Refines}\left(optimalActions, concept\right)\right)\right) \land \operatorname{let} predictionExample: Bool \to \operatorname{PMF}\left(Bool\right), \forall state \in Bool,\; predictionExample\left(state\right) = \operatorname{pure}\left(state\right); \operatorname{let} lossExample: Bool \to \left(Bool \to \mathbb{R}\right), \forall action \in Bool, outcome \in Bool,\; lossExample\left(action, outcome\right) = \operatorname{if}\left(action, 0, \operatorname{if}\left(outcome, 2, 1\right)\right); \operatorname{let} expectedLossExample: Bool \to \left(Bool \to \mathbb{R}\right), \forall state \in Bool, action \in Bool,\; expectedLossExample\left(state, action\right) = \operatorname{integral}\left(\operatorname{toMeasure}\left(predictionExample\left(state\right)\right), lossExample\left(action\right)\right); \operatorname{let} optimalActionsExample: Bool \to \operatorname{Set}\left(Bool\right), \forall state \in Bool,\; optimalActionsExample\left(state\right) = \left\{action: Bool \mid \forall alternative \in Bool,\; expectedLossExample\left(state, action\right) \le expectedLossExample\left(state, alternative\right)\right\}; \operatorname{let} conceptExample: Bool \to Unit, \forall state \in Bool,\; conceptExample\left(state\right) = unit; \operatorname{Refines}\left(optimalActionsExample, conceptExample\right) \land \neg \operatorname{Refines}\left(predictionExample, conceptExample\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiencyStrictness.prediction_sufficiency_implies_decision_sufficiency_strictly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factoring a predictive PMF through a concept factors both its complete expected-loss profile and the optimizer-set readout through that concept.

The converse countermodel uses two distinct deterministic predictive laws. Its outcome-dependent loss makes true the unique optimizer in both states, so one constant concept determines the actions but not the predictive law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiencyStrictness.prediction_sufficiency_implies_decision_sufficiency_strictly`
- Dependency: [D5/S3/ConceptDynamics/Decision/PredictionLawDecisionSufficiency](PredictionLawDecisionSufficiency.md)
