# Role Admission and Contamination Closure

## Abstract

Snapshot-bounded judge admission is unchanged by ledger events appended after the snapshot adjudication point.

**Theorem 1.1 (Later ledger events cannot flip frozen-round admission).**

$$\forall L, \Delta, K_{n},\\{}(\forall e, (e \in \Delta \Rightarrow adjudicationPoint(K_{n}) < eventNumber(e))) \Rightarrow (\forall r, AdmissibleJudge(L ++ \Delta, r, K_{n}) \iff AdmissibleJudge(L, r, K_{n})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure.admissible_judge_append_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen commitment carries its own round, freeze point, and adjudication point. Judge admission therefore has no independent caller-supplied cutoff or round.

Both recorded roles and adaptive uses inspect only role events whose event number is at most the snapshot adjudication point. The admission predicate also requires a post-freeze first-seen time, exclusion from the reflexive-transitive dependency closure, and absence of adaptive use.

If every appended event is strictly later than that adjudication point, none enters either cutoff-filtered ledger query. Admission is therefore identical before and after the append; future Tune and Adjudicate events are explicit instances.

The companion formal specification defines contamination as reachability from a record set. Thus derived functions, digests, labels, human selections, and trained intermediates remain source-graph facts; hiding an original identifier does not alter admission.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure.admissible_judge_append_invariant`
