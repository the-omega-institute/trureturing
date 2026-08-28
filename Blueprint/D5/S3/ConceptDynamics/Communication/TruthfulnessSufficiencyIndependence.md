# Truthfulness and Sufficiency

## Abstract

Truthful reporting and target sufficiency jointly yield a sufficient sent report, while neither condition implies the other.

**Theorem 1.1 (Reporting honesty and sufficiency are independent factors).**

$$\begin{gathered}\forall State, Message, Target: \operatorname{Type}^{*},\\{}profile: \operatorname{ReportProfile}\left(State, Message, Target\right),\\{}(R_{send}^{profile} = R_{true}^{profile} \Rightarrow T^{profile} = \overline{T}^{profile} \circ R_{true}^{profile} \Rightarrow T^{profile} = \overline{T}^{profile} \circ R_{send}^{profile}) \land\\{}(\exists h: \operatorname{ReportProfile}\left(Bool, Unit, Bool\right), R_{send}^{h} = R_{true}^{h} \land T^{h} \neq \overline{T}^{h} \circ R_{true}^{h}) \land\\{}(\exists s: \operatorname{ReportProfile}\left(Bool, Bool, Bool\right), R_{send}^{s} \neq R_{true}^{s} \land T^{s} = \overline{T}^{s} \circ R_{true}^{s}) \land\\{}(\exists b: \operatorname{ReportProfile}\left(Bool, Bool, Bool\right), R_{send}^{b} = R_{true}^{b} \land T^{b} = \overline{T}^{b} \circ R_{true}^{b}) \land\\{}(\exists n: \operatorname{ReportProfile}\left(Bool, Bool, Bool\right), R_{send}^{n} \neq R_{true}^{n} \land T^{n} \neq \overline{T}^{n} \circ R_{true}^{n}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/TruthfulnessSufficiencyIndependence.truthfulness_sufficiency_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A report profile publicly contains a target on states, the report that the state warrants, the report actually sent, and a decoder from messages to target values.

Equality of the sent and truthful mechanisms transports a factorization through the truthful mechanism to the sent mechanism. This is the forward trust clause.

Four concrete finite profiles establish the two independent axes. A Unit message space is honest but too coarse; a Boolean identity report with a negated sent message is sufficient but dishonest; identity mechanisms satisfy both; and distinct constant reports with a varying target satisfy neither.

Repository and pinned-library searches found no exact report-factorization theorem. Loogle missed, and LeanSearch returned only probabilistic notions of independence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/TruthfulnessSufficiencyIndependence.truthfulness_sufficiency_independence`
