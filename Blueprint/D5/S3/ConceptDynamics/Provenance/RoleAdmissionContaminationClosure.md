# Role Admission and Contamination Closure

## Abstract

Snapshot-bounded judge admission is unchanged by ledger events appended after the snapshot adjudication point, when both traces are valid.

**Theorem 1.1 (Later ledger events cannot flip frozen-round admission).**

$$\forall L, Lprime, K_{n}, v, vprime, h, r\\{}(ValidTrace(L, K_{n}, v) \land ValidTrace(Lprime, K_{n}, vprime) \land AppendOnlyExtension(L, Lprime, K_{n}, h)) \Rightarrow (AdmissibleJudge(Lprime, K_{n}, vprime, r) \iff AdmissibleJudge(L, K_{n}, v, r)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure.admissible_judge_append_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen commitment carries its own round, freeze event, decision event, filtration, dependency closure, and evidence-dependency set. Judge admission therefore has no independent caller-supplied cutoff or round.

Both recorded roles and adaptive uses inspect only events in the validated event, round, and time prefix. The admission predicate requires adjudication role presence, absence at freeze, absence from the snapshot dependency set, and absence of adaptive use.

If every appended event is strictly later than the decision event, none enters the event prefix. With ValidTrace proofs on both ledgers, admission is therefore identical before and after the append.

The companion formal specification defines contamination as reachability from a record set. Thus derived functions, digests, labels, human selections, and trained intermediates remain source-graph facts; hiding an original identifier does not alter admission.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure.admissible_judge_append_invariant`
