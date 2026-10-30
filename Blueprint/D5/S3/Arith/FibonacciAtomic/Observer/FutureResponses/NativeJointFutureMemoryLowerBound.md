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

Choosing one source from each memory fibre gives a surjection from W onto the eleven attained joint classes. Finite cardinality then forces eleven to be at most the number of memory states.

More generally, let memory be any map from Source to a finite W, without requiring it to be surjective, and suppose the same memoryReadout reproduces futureReplies(u,k) for every source u and every natural k. Write R = range(memory) for its realized image. The map Set.rangeFactorization memory sends u to memory(u), regarded as an element of R, and is surjective onto R. Restrict memoryReadout to R by composing with the subtype inclusion R to W. The displayed theorem applied to this finite carrier gives 11 <= card(R). The inclusion also gives card(R) <= card(W), so unused carrier states do not count toward the eleven required realized states.

Equivalently, equality of encoded memory values implies equality of all future replies and hence equality of jointClass. Applying realized_image_unique_factorization_iff_reverse_kernel with coarse readout jointClass and fine readout memory gives a unique map from R to the realized joint classes that recovers jointClass from the encoded memory of every source. Since every joint class is attained, this factor is surjective onto all eleven classes.

This is static memory for the two-address futureReplies task: both addresses [true,false] and [true,true] are read in the initial tree .mul (.of true) u for one common u : Source, after the same supplied substitution count. A fibre of the replies at one fixed count can contain different all-future classes: the alpha and beta right-subtree sources agree at count zero and differ at count one. An executable adaptive controller must additionally supply lawful updates and action selection; these memory bounds do not construct one or determine its full state count.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound.native_joint_future_memory_lower_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses](NativeJointFutureClasses.md)
