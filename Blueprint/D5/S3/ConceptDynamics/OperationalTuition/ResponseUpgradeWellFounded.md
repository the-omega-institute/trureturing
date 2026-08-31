# Response Upgrade Well-Foundedness

## Abstract

Finite T2-compliant response traces cannot retry forever: a sufficiently long same-stimulus trace must stop or change class, and blind retries are decidable.

**Theorem 1.1 (T2 response traces stop or change class).**

$$\begin{aligned}\forall S, C, R: Type,\\{}[\operatorname{Fintype}\left(S\right)], [\operatorname{Fintype}\left(C\right)], [\operatorname{Fintype}\left(R\right)],\\{}[\operatorname{DecidableEq}\left(S\right)], [\operatorname{DecidableEq}\left(C\right)], [\operatorname{DecidableEq}\left(R\right)],\\trace: \operatorname{List}\left(\operatorname{ResponseEvent}\left(S, C, R\right)\right),\\stimulus: S, responseClass: C,\\\operatorname{T2Compliant}\left(trace\right) \Rightarrow \forall event: \operatorname{ResponseEvent}\left(S, C, R\right), event \in trace \Rightarrow \operatorname{stimulus}\left(event\right) = stimulus \Rightarrow \operatorname{card}\left(R\right) < \operatorname{length}\left(trace\right) \Rightarrow \exists event, event \in trace \land (\operatorname{stopped}\left(event\right) = true \lor \operatorname{responseClass}\left(event\right) \neq responseClass).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded.t2_response_upgrade_well_founded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A response event records a stimulus, response class, response value, and an explicit stop bit. T2 compliance is a structural predicate requiring the nonterminal responses in each finite stimulus/class slice to be duplicate-free.

The finite response alphabet bounds every duplicate-free list by its Fintype cardinality. If a same-stimulus trace exceeds that bound, the compliant trace therefore contains a stopping event or an event whose response class has changed.

**Theorem 1.2 (Blind-retry T2 violations are decidable).**

$$\begin{aligned}\forall S, C, R: Type,\\{}[\operatorname{Fintype}\left(S\right)], [\operatorname{Fintype}\left(C\right)], [\operatorname{DecidableEq}\left(S\right)], [\operatorname{DecidableEq}\left(C\right)], [\operatorname{DecidableEq}\left(R\right)],\\trace: \operatorname{List}\left(\operatorname{ResponseEvent}\left(S, C, R\right)\right),\\\operatorname{t2ViolationDecision}\left(trace\right) = true \iff \neg \operatorname{T2Compliant}\left(trace\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded.t2_violation_decidable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All carriers and the finite trace are explicit, so the universal T2 predicate has a decision procedure. The Boolean classifier returns true exactly for its negation.

A two-event trace repeating the sole response in a one-element alphabet is a compiled blind-retry witness and is classified as a violation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded.t2_response_upgrade_well_founded`
- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded.t2_violation_decidable`
