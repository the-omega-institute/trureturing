# Connected exclusion response calibration

## Abstract

One zero seed calibrates the same response on every finite connected exclusion graph.

**Definition 1.1 (Original configuration family).**

$$\forall V: \operatorname{Type}, [\operatorname{Fintype}(V)], [\operatorname{DecidableEq}(V)], G: \operatorname{SimpleGraph}(V), S: \operatorname{Finset}(\operatorname{Finset}(V)), \operatorname{IsRecordFamily}(G, S) \iff (\emptyset \in S \land (\forall k: V, \{k\} \in S) \land (\forall t: \operatorname{Finset}(V), t \in S \Rightarrow \operatorname{IsIndepSet}(G, t))).$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.IsRecordFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite vertex type and finite family retain the empty configuration and every singleton. Every allowed output is independent in the same graph.

**Definition 1.2 (Original bit marginal).**

$$\forall V: \operatorname{Type}, [\operatorname{Fintype}(V)], [\operatorname{DecidableEq}(V)], S: \operatorname{Finset}(\operatorname{Finset}(V)), T: S \to S \to \mathbb{R}, k: V, s: S, \operatorname{marginal}(S, T, k, s) = \sum_{t: S} \operatorname{if} k \in t \operatorname{then} T(t, s) \operatorname{else} 0.$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.marginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both arguments of T range over the same original family S. The first argument is the reported output and the second is the source; the sum never renames either configuration.

**Definition 1.3 (Same-response hypotheses).**

$$\forall V: \operatorname{Type}, [\operatorname{Fintype}(V)], [\operatorname{DecidableEq}(V)], S: \operatorname{Finset}(\operatorname{Finset}(V)), T: S \to S \to \mathbb{R}, a: V \to \mathbb{R}, b: V \to \mathbb{R}, \operatorname{ResponseLaws}(S, T, a, b) \iff (\forall t: S, s: S, 0 \leq T(t, s)) \land (\forall s: S, \sum_{t: S} T(t, s) = 1) \land (\forall k: V, s: S, \operatorname{marginal}(S, T, k, s) = \operatorname{if} k \in s \operatorname{then} b(k) \operatorname{else} a(k)) \land (\forall k: V, a(k) = 0 \Rightarrow b(k) = 1).$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.ResponseLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The columns are nonnegative and sum to one. A bit marginal depends only on whether that same bit occurs in the source. Support compatibility is the one-sided implication from a zero off-source marginal to a unit on-source marginal.

**Theorem 1.4 (Whole original R5-002 Theorem 5.1).**

$$\forall V: \operatorname{Type}, [\operatorname{Fintype}(V)], [\operatorname{DecidableEq}(V)], G: \operatorname{SimpleGraph}(V), S: \operatorname{Finset}(\operatorname{Finset}(V)), T: S \to S \to \mathbb{R}, a: V \to \mathbb{R}, b: V \to \mathbb{R}, (\operatorname{IsRecordFamily}(G, S) \land \operatorname{ResponseLaws}(S, T, a, b) \land \operatorname{Connected}(G) \land (\exists k: V, a(k) = 0)) \Rightarrow (\forall k: V, a(k) = 0 \land b(k) = 1) \land (\forall t: S, s: S, T(t, s) = \operatorname{if} t = s \operatorname{then} 1 \operatorname{else} 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.connected_response_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement is Theorem 5.1 of AURIC_R5_002_THREE_PHASE_COMPARISON_INTERNAL_RECORDS_AND_QUANTUM_AXIOMS, with the finite independent-set family represented by a Finset of Finsets. Connected includes a nonempty vertex type. No nontriviality, extra neighbor or per-vertex seed is assumed; a connected singleton is included.

For adjacent vertices i and j, independence of every output gives p(i,s)+p(j,s) at most one for the original column s. In the singleton source {i}, a(i)=0 and support compatibility force p(i,{i})=1. The other marginal is a(j), while the empty source proves its nonnegativity. Hence a(j)=0. A walk from the one seed propagates this calibration to every vertex.

A positive transition must preserve every bit: if an output has a bit absent from its source, its mass is bounded by the now-zero marginal; if it lacks a source bit, its mass is bounded by the now-zero complementary marginal. Extensionality of the original finite configurations eliminates every wrong outcome. Normalization gives mass one to the unchanged source name.

Mathlib supplies SimpleGraph.IsIndepSet, connected reachability, walk elimination and finite nonnegative-sum bounds. The graph-wide calibration and support-rigidity argument supplies the additional relation. This unit asserts no supply of physical zero seeds or gate orbits, no disconnected-graph conclusion, and no Hilbert reconstruction or Theorem 5.2/5.3 endpoint.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.IsRecordFamily`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.ResponseLaws`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.connected_response_calibration`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.marginal`
