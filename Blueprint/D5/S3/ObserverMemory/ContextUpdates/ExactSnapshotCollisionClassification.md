# Exact Snapshot Collision Classification

## Abstract

Exact decoding and source injectivity are characterized by collisions on reachable branches.

**Theorem 1.1 (Two collisions determine both signed differences).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_collision_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_collision_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be an additive commutative group, let chi:G to ZMod 2 be surjective, and let I be a finite sender set with at least three elements, so a third sender exists for two distinct senders. On a fixed parity fibre, exactness means that equal replies force equal sums of sender inputs.

Exactness separates each reply map on both chi fibres. Thus a nontrivial collision has odd difference. If sender i collides at x and y and sender j collides at u and v, a third sender completes the parity in two source comparisons. The first comparison changes both coordinates and gives (y-x)+(v-u)=0; the second changes the first coordinate against the opposite change and gives (y-x)-(v-u)=0.

The two equations are obtained while the parity, branch and all replies remain fixed; they therefore apply to arbitrary partial collisions on that branch.

**Theorem 1.2 (All nontrivial collision differences agree).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.common_odd_collision_of_two_senders`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.common_odd_collision_of_two_senders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two distinct senders each have a nontrivial collision on an exact branch, their collision differences are equal and are fixed by a single element tau.

The element tau has chi(tau)=1 and 2 tau=0. Every collision of every sender on the branch has difference tau, while a sender with no collision imposes no condition. The collision family may therefore be partial and the exceptional sender may depend on the branch.

**Theorem 1.3 (A decoder induces exactness on every reachable parity branch).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_decoder`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an existing deterministic protocol and decoder that recovers the target on every source, fix a reachable (a,t,c). Any sender tuple whose sum has parity chi(t-a) can be completed with the unique kernel-valued clock offset. Two such tuples with equal replies produce equal observations, so decoder correctness forces equal sender sums.

**Theorem 1.4 (Collision conditions imply branch exactness).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_condition`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose each reply map separates equal-characteristic inputs and either at most one sender is noninjective or all nontrivial collisions have one common odd involution.

On a fixed characteristic fibre, equal replies then force equal sender sums. With one possible exceptional sender, parity determines its characteristic and separation determines its value. With a common involution, each coordinate difference is zero or the involution, and the parity equation makes the total difference zero.

**Theorem 1.5 (Exact recovery is equivalent to the branch collision conditions).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.exact_recovery_iff_branch_conditions`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.exact_recovery_iff_branch_conditions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a surjective characteristic and a finite set of at least three senders, a deterministic protocol has a decoder recovering the target on all sources exactly when every reachable branch has fibre separation and satisfies the one-exception-or-common-involution alternative.

The reverse implication constructs a decoder by assigning to each observation the unique target value on its source fibre; observations outside the image receive an arbitrary value. Empty branches therefore impose no condition, and collision pairs may remain partial or vary between branches.

**Theorem 1.6 (Source injectivity is equivalent to at most one noninjective sender per branch).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.source_injective_iff_branch_single`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.source_injective_iff_branch_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the protocol has an exact decoder. The observation map is injective on the actual source space exactly when every reachable branch has at most one noninjective sender.

If two senders collide, the common odd involution and a third sender produce two distinct sources with the same observation. If at most one sender is noninjective, fibre separation and the parity constraint recover every sender coordinate, after which the clock equation recovers the kernel offset.

## References

- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_collision_rigidity`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_condition`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_decoder`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.common_odd_collision_of_two_senders`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.exact_recovery_iff_branch_conditions`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.source_injective_iff_branch_single`
- Dependency: [D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotPeriodClassification](ExactSnapshotPeriodClassification.md)
