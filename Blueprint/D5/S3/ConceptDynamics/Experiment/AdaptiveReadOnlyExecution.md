# Adaptive Read-Only Execution

## Abstract

Adaptive read-only controllers retain dependent responses and charge distinct queries.

**Definition 1.1 (History controller).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Controller`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing Hist(Y) carrier is a finite list of dependent query-response pairs. A controller maps only this record to an optional sum of a query action and a return value. None denotes a stall. Source, action, dependent response, and return types are arbitrary; no finiteness is required.

**Definition 1.2 (History consistency).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Consistent`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Consistent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each recorded dependent response equals read(a,x) for the same fixed source x. Queries read the source without changing it.

**Definition 1.3 (Distinct query set).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.queries`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.queries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mapping the history to its actions and taking toFinset retains exactly the distinct queries. This definition requires decidable equality on actions.

**Definition 1.4 (Distinct query count).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.queryCount`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.queryCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge is the cardinality of the distinct query set. Repeated queries are allowed and contribute no additional charge.

**Definition 1.5 (Finite execution relation).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Run`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Run(read,pi,x,pre,t,b) retains the additional ordered record t after prefix pre and returns b. Its stop constructor records an immediate return; its query constructor appends the actual dependent response before continuing. There is no fuel or height bound and no constructor for a stall. The controller observes only the preceding record.

**Definition 1.6 (Total finite correctness).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Correct`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Correct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every source x there exists a finite run from the empty history returning target(x). This imposes no uniform bound on finite execution lengths.

**Definition 1.7 (Extended execution cost).**

Lean statement: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.cost`

*Formalization.* `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.cost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cost takes the extended nonnegative infimum of distinct-query counts over all finite run witnesses and return values. With no finite witness the infimum is top, including stalled and infinite query executions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Consistent`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Controller`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Correct`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.Run`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.cost`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.queries`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.queryCount`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](PassivePolicyNormalization.md)
