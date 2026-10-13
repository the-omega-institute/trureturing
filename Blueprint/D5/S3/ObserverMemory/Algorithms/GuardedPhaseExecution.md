# Guarded Phase Execution

## Abstract

Guarded weighted paths characterize finite executions on one original source.

A fixed instruction table uses control states Q, addresses A and replies R. One observation field assigns a reply to each epoch and address. For an original source u with transport U, the intended field is the literal read on U iterated j times at epoch j. The same field is used in every phase.

**Definition 1.1 (Literal reads, unit updates and halts).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Instruction`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Instruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A read instruction installs one address and a successor for every reply. An update has one successor and increments the epoch by one. A halt has no outgoing edge. The instruction table does not inspect the source or epoch.

**Definition 1.2 (Finite actual paths).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Run`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual path keeps its initial and terminal controls and epochs. Reads use the fixed source's observation field at the current epoch; updates advance that epoch exactly once. The empty path is allowed. A path ending at a halt cannot have passed through an earlier halt.

**Definition 1.3 (Paths under one fixed response vector).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.FixedPath`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.FixedPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every read uses the chosen response vector. The weight records exactly the number of updates, with zero contribution from reads. Endpoints are retained, including cuts inside update-containing cycles.

**Definition 1.4 (A boundary is crossed by a final update).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Crossing`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Crossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A crossing consists of a fixed-response path followed by one update. Its total weight is one plus the preceding path's weight. Consequently all reads occur strictly before the endpoint epoch. A pure-read cycle cannot supply a crossing into a later epoch.

**Definition 1.5 (One source supplies the whole phase).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Guard`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Guard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guard requires equality of the observation field and the response vector at every epoch in a half-open interval. Addresses can be labels for the installed read states, so this asserts exactly the common response vector without adding an online simultaneous-read instruction.

**Definition 1.6 (Strict phase boundaries and a terminal delimiter).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Partition`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonempty list records each interval's right endpoint and response vector. Endpoints increase strictly, adjacent intervals meet, every interval satisfies its guard, and the final endpoint is the specified delimiter. Adjacent vectors may agree; maximality is not required.

**Definition 1.7 (Endpoint-compatible phase certificates).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.PhasePaths`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.PhasePaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every internal segment is a crossing to the next phase's starting control. The final segment is a fixed-response path to the requested terminal control and epoch J. Its delimiter is J plus one, which includes reads at J and does not perform an update after halt. This last path may be empty.

**Theorem 1.8 (Exact equivalence with actual execution).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.guarded_phase_execution`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.guarded_phase_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every guarded partition from the starting epoch through J, phase paths exist exactly when an actual finite path connects the same initial and terminal controls at those epochs. This holds for arbitrary state, address and reply types; finiteness is unnecessary for the semantic equivalence.

To split an actual path, locate the unit update that first enters an internal boundary epoch. The preceding segment ends one epoch before the boundary, so its entire read range satisfies the old guard. Repeat on the remaining actual path. Conversely, each guard converts its fixed-response path into actual steps, and the exact endpoints allow their concatenation.

When the terminal control is a halt, the equivalence is about its first arrival. It imposes no action-count bound and no termination assumption. A finite bound on the number of phases and an effective arithmetic description of fixed-response paths are separate hypotheses needed for a uniform arithmetic synthesis procedure.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Crossing`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.FixedPath`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Guard`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Instruction`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Partition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.PhasePaths`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.Run`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.guarded_phase_execution`
