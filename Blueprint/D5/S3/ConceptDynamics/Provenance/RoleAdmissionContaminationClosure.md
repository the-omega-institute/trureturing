# Role Admission and Contamination Closure

## Abstract

Snapshot-bounded judge admission is unchanged by ledger events appended after the snapshot adjudication point, when both traces are valid.

**Theorem 1.1 (Later ledger events cannot flip frozen-round admission).**

$$\forall L, Lprime, K_{n}, (v : ValidTrace(L, K_{n})), (vprime : ValidTrace(Lprime, K_{n})), (h : AppendOnlyExtension(L, Lprime, K_{n})), r\\{}(AdmissibleJudge(Lprime, K_{n}, vprime, r) \iff AdmissibleJudge(L, K_{n}, v, r)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure.admissible_judge_append_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen commitment carries its own round, freeze event, decision event, access-derived filtration, and commitment roots. Judge admission therefore has no independent caller-supplied cutoff or round.

Both recorded roles and adaptive uses inspect only events in the validated event, round, and time prefix. The admission predicate requires adjudication role presence, first access strictly after freeze, absence from the incoming closure of records that reach a commitment root, and absence of adaptive use.

If every appended event is strictly later than the decision event, none enters the event prefix. With ValidTrace proofs on both ledgers, admission is therefore identical before and after the append.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure.admissible_judge_append_invariant`
