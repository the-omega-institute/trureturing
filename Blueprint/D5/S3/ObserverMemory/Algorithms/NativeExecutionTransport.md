# Native Execution Transport

## Abstract

Native transport and halt endpoint uniqueness preserve literal execution.

**Definition 1.1 (Control equivalence and literal address mapping).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.transport`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A control equivalence maps every successor. An arbitrary address map maps the literal installed at each read; distinct occurrences may share one physical literal. Replies retain their type and meaning.

**Definition 1.2 (The reindexed instruction table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.transportProgram`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.transportProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table at a new control evaluates the original table at its inverse control, then maps that instruction. It adds no source or epoch port.

**Theorem 1.3 (Exact native execution transport in both directions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.run_transport_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.run_transport_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exact instruction compatibility and equality of observations at every epoch and mapped address, a native Run exists exactly when the reindexed Run exists. Both initial and terminal epochs are unchanged. The same original source observation is used at every read.

The reverse direction inspects the original instruction at the inverse control and identifies its mapped successor. It needs no inverse, injectivity or surjectivity of the address map. No finite carrier or termination assumption is used.

**Theorem 1.4 (Halt-ended executions agree in control and epoch).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.run_halt_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.run_halt_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two native Runs from the same control and epoch on the same observation field have equal endpoint controls and epochs when both endpoint instructions are halt. Deterministic reads and updates force their successors to agree, and a halt has no outgoing edge.

Arbitrary finite endpoints are not unique: the empty path and a longer prefix can coexist. This result provides the native operational prerequisite for whole-table synthesis; it constructs no synthesis algorithm and does not settle the uniform descriptor boundary theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.run_halt_unique`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.run_transport_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.transport`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.transportProgram`
- Dependency: [D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution](GuardedPhaseExecution.md)
