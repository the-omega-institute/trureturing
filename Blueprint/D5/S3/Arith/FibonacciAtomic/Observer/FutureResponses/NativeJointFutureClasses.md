# Native Joint Future Classes

## Abstract

A native source is an ordered binary tree with alpha and beta leaves. Substitution sends alpha to beta, beta to the ordered pair beta-alpha, and acts on both children of a branch. The initial source is the pair of alpha and an arbitrary finite right subtree. The supplied count is the same for both addresses RL and RR.

**Theorem 1.1 (Native Joint Future Classes).**

$$(\forall u,v:Source,(\forall k\in \mathbb{N},\operatorname{futureReplies}(u,k)=\operatorname{futureReplies}(v,k))\Leftrightarrow \operatorname{jointClass}(u)=\operatorname{jointClass}(v))\land \operatorname{Surjective}(jointClass)\land \operatorname{card}(JointClass)=11$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses.native_joint_future_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A native source is an ordered binary tree with alpha and beta leaves. Substitution sends alpha to beta, beta to the ordered pair beta-alpha, and acts on both children of a branch. The initial source is the pair of alpha and an arbitrary finite right subtree. The supplied count is the same for both addresses RL and RR.

The right subtree has two leaf classes. If it is a branch, the complete future reply at each child is determined by whether that child initially is alpha, beta or a branch. These nine pairs are jointly realized by pairing canonical root representatives inside one source. A branch stays a branch for every future count. The two leaf cases and the nine branch cases are distinct; no bound on the tree height or on the future count is imposed.

Equality of the two reply trajectories at every supplied count is equivalent to equality of the eleven-valued joint class. Generic minimum sufficient coding is supplied by target_family_minimal_quotient; the native calculation specifies its attained joint fibers.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureClasses.native_joint_future_classification`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](../../ActualTreeReadoutAcquisition.md)
