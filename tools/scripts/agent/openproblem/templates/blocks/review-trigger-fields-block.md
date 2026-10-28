
## Blocking-finding contract (sshx beta.49, binding)
Each blocking finding must name both of the following:
- the GoalArtifact term the delivery fails: a `normalized_goal` clause, a `constraints` item or a `success_criteria` item, or the CLAUDE.md rule cited in this brief;
- the evidence in the delivered branch that shows the failure: file:line, a failing command with its exit code, or a wrong value.

It must also carry these fields:
- `trigger`: the state or input that causes the failure;
- `trigger_actor`: who or what created that state;
- `trigger_path`: exactly `ordinary-operation`, `nonstandard-deliberate` or `malicious`;
- `mechanism_family`: a stable label for the mechanism;
- `recorded_occurrence`: a pre-run, independently existing incident, PR verdict or documented precedent, or `none`.

A finding whose `trigger_path` is not `ordinary-operation` and whose `recorded_occurrence` is `none` is advisory, not blocking. Fixtures you create during this review show reachability only; they are not recorded occurrences. Findings that name fewer than both conjuncts are advisory.
