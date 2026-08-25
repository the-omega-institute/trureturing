# Four-Way Uncertainty Independence

## Abstract

Finite source models realize every truth profile of four uncertainty kinds.

**Theorem 1.1 (All four-way uncertainty truth profiles are realizable).**

$$\begin{gathered}\forall p: \operatorname{Fin}\left(4\right) \to Bool,\\{}C: Bool \to Bool, C(x) := \operatorname{if}\left(p(0) = true, false, x\right),\\{}Supp: Bool \to Unit \to Bool \to Prop, Supp(x, u, y) := p(1) = true \lor y = false,\\{}Compat: Bool \to Prop, Compat(m) := True, Pred: Bool \to Unit \to Bool,\\{}Pred(m, t) := \operatorname{if}\left(p(2) = true, m, false\right), Pref: Bool \to Bool \to Bool \to Prop,\\{}Pref(i, a, b) := p(3) = true \land ((i = false \land a = true \land b = false) \lor (i = true \land a = false \land b = true)),\\{}Epistemic := \neg \operatorname{Injective}\left(C\right), Aleatoric := \exists x: Bool, u: Unit, y, z: Bool, y \neq z \land Supp(x, u, y) \land Supp(x, u, z),\\{}ModelUncertainty := \exists m, n: Bool, t: Unit, m \neq n \land Compat(m) \land Compat(n) \land Pred(m, t) \neq Pred(n, t),\\{}Normative := \exists i, j, a, b: Bool, i \neq j \land a \neq b \land Pref(i, a, b) \land Pref(j, b, a),\\{}(Epistemic \iff p(0) = true) \land\\{}(Aleatoric \iff p(1) = true) \land\\{}(ModelUncertainty \iff p(2) = true) \land\\{}(Normative \iff p(3) = true).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Uncertainty/FourWayIndependence.four_uncertainties_have_all_truth_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The profile p assigns independent truth values to epistemic, aleatoric, model, and normative uncertainty.

Evidence switches between identity and a constant readout. Future support switches between a singleton and both Boolean outcomes. Prediction switches between a constant and the model bit, while preference switches between no rankings and two opposed rankings.

Each uncertainty predicate is defined from its source primitive: evidence noninjectivity, two distinct supported futures, compatible models with distinct predictions, and distinct doctrines with opposite rankings of distinct actions.

The four public equivalences hold for every p. Thus all sixteen truth profiles occur, including a model with any chosen uncertainty true and any other chosen uncertainty false, so no general implication exists between distinct kinds.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Uncertainty/FourWayIndependence.four_uncertainties_have_all_truth_profiles`
