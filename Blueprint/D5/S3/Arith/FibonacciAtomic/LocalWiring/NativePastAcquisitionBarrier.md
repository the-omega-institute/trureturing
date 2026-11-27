# Past native acquisition and the update barrier

## Abstract

Under the native serial service, finite past acquisition does not expose bits newer than the mature word at the final cut.

**Theorem 1.1 (Exact trace replay and the two class-uniform barriers).**

$$n\ge 2, v_{n}=F_{n}-1\quad v_{n}< 2d,\quad v_{n}< 2K-1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/NativePastAcquisitionBarrier.native_past_acquisition_barrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two strict inequalities are separate subthreshold conditions: the first for unknown-order Boolean recurrences of public cap d≥0, the second for nonempty autonomous unary Moore sources of cap K≥1. The trace assertion itself holds also at the fixed cuts zero and one.

A common source-blind observer starts at alpha and makes serial literal Reads, actual Updates with a common acknowledgement, arbitrary source-free local changes and retention, or a local stop. Decisions see only the public input, common independent tape and accessible record. The record retains requested physical addresses, replies, local events, state and retained data. No label snapshot, private source data, physical duration or extra observation is provided.

Every finite prefix ending no later than a chosen cut is equal to replaying from its mature word with fixed padding, on identical public inputs and tape. The prefix need not be terminal and there is no common bound on local or service steps. For equal mature words, every record event at the fixed cut has the same tape preimage under both sources.

Below the appropriate threshold, no common observer and answer decoder can stop correctly at the fixed cut eventually under one shared proper tape filter for every lawful source, for any of the three tasks separately: full current labels, all next-cut literal presence replies, or complete finite future behavior. The two task-specific successes would be disjoint tape events but both eventual. This applies in particular to a shared almost-sure tape law. It does not bound paid reads or search work, and does not assert a fixed difficult source or a per-fiber failure.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/NativePastAcquisitionBarrier.native_past_acquisition_barrier`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/LawfulSourceReadiness](LawfulSourceReadiness.md)
