# Native Joint Future Memory Lower Bound

## Abstract

Exact native future-response classes impose an eleven-state finite-memory lower bound.

**Theorem 1.1 (A finite memory preserving all native future replies has at least eleven states).**

$$\forall W: Type, [\operatorname {Fintype}(W)] \forall memory: Source \to W, {\forall memoryReadout: W \to \mathbb {N} \to \operatorname {Prod}(Reply, Reply), {{\operatorname {Surjective}(memory) \land \forall u: Source, {\forall k: \mathbb {N}, {\operatorname {futureReplies}(u, k) = \operatorname {memoryReadout}(\operatorname {memory}(u), k)}}} \Rightarrow 11 \leq \operatorname {card}(W)}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound.native_joint_future_memory_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be a finite memory carrier. A surjective memory map assigns every native source to a memory state, and memoryReadout must reproduce the two future replies for every supplied count from that state.

If two sources share one memory state, their reproduced future reply trajectories agree. The native eleven-class classification therefore assigns the same joint class to every source in that memory fibre.

Choosing one source from each memory fibre gives a surjection from W onto the eleven attained joint classes. Finite cardinality then forces eleven to be at most the number of memory states. The result counts future-behaviour states only; an executable controller may require additional phase or action-selection states.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound.native_joint_future_memory_lower_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses](NativeJointFutureClasses.md)
