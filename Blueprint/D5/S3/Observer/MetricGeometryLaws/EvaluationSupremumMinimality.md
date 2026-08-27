# Evaluation Supremum Minimality

## Abstract

Evaluation suprema are the least pseudometrics dominating every readout distance.

**Theorem 1.1 (State and protocol evaluation suprema are least dominating).**

$$\begin{gathered}\forall X, P, \Lambda: \operatorname{Type},\\{}\operatorname{PseudoMetricSpace}(\Lambda), e: X \to \left(P \to \Lambda\right),\\{}\delta_{X}: \operatorname{PseudoMetricSpace}(X), \delta_{P}: \operatorname{PseudoMetricSpace}(P),\\{}((\forall x, y \in X, \forall p \in P,\ \operatorname{dist}(d_{\Lambda}, \operatorname{eval}(e, x, p), \operatorname{eval}(e, y, p)) \leq \operatorname{dist}(\delta_{X}, x, y)) \Rightarrow \forall x, y \in X,\ \operatorname{sup}_{p \in P} \operatorname{dist}(d_{\Lambda}, \operatorname{eval}(e, x, p), \operatorname{eval}(e, y, p)) \leq \operatorname{dist}(\delta_{X}, x, y))\\{}\land\\{}((\forall p, q \in P, \forall x \in X,\ \operatorname{dist}(d_{\Lambda}, \operatorname{eval}(e, x, p), \operatorname{eval}(e, x, q)) \leq \operatorname{dist}(\delta_{P}, p, q)) \Rightarrow \forall p, q \in P,\ \operatorname{sup}_{x \in X} \operatorname{dist}(d_{\Lambda}, \operatorname{eval}(e, x, p), \operatorname{eval}(e, x, q)) \leq \operatorname{dist}(\delta_{P}, p, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality.evaluation_suprema_are_least_dominating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lambda is a pseudometric law carrier, e evaluates a state-protocol pair, and delta_X and delta_P are arbitrary competitor pseudometrics on the exact source carriers.

The two displayed suprema are the canonical source constructions. Any pointwise upper bound for every state readout bounds the state supremum, and the same least-upper-bound argument applies to protocol responses.

The surrounding bounded-law assumption is not needed for this stronger minimality statement: each competitor hypothesis already supplies the required upper bound.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality.evaluation_suprema_are_least_dominating`
