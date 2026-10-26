# Critical renewal Paths

## Abstract

One uninterrupted actual history.

**Theorem 1.1 (One uninterrupted actual history).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.consecutive_block_event`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.consecutive_block_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau be any natural initial wait and let blocks be any sequence of finite zero-coin lists with closing-tick coins. Put clock(n)=tau+1+sum over h<n of (length(zeros(h))+1). For every n and k at most length(zeros(n)), event(clock(n)+k) is (zero, the kth zero coin) when k is smaller than that length, and (one, the block tick coin) at equality.

event is zero throughout the initial wait and one at its closing tick. The clock is strictly increasing and unbounded, so every later read has one block address. These addresses and coin lists are analytical coordinates. The successor function receives only the current counted state, actual bit and fresh outcome.

**Theorem 1.2 (Exact counted stopped-prefix payment).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.stopped_prefix_payment`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.stopped_prefix_payment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive H, natural J, immutable Tick J, a natural initial wait tau, a sequence of finite blocks and a natural g. Write E(n) for the sum of the first n block increments. Suppose E(g) lies outside the open interval (-H,H) and E(n) lies inside it for every n<g.

Then the first gap threshold time gapStop equals g. The first paid label time paidStop equals exactly 1+tau+sum over n<g of (length(zeros(n))+1). At clock(g) the actual run equals target(E(g)), and at every strictly earlier bit prefix it is not a label. The emitted label is one if and only if E(g) is at least H, and zero if and only if E(g) is at most -H.

For every n<g and k at most that block's zero count, the run at clock(n)+k is precisely evidence E(n) and the phase obtained from that same block's first k zero outcomes. For every nonzero real grid spacing delta and every n, E(n)=score(delta,n)/delta, where score is the ordinary real sum of the increments multiplied by delta. The same carrier has exact cardinality 3+(2H-1)(J+1).

Every failed or holding interval, every dead suffix, the first wait, the first tick and the terminal closing tick is charged. There is no terminal partial interval and no stopping-time label decoder. Potential blocks after termination are an analytical continuation of the same history.

**Theorem 1.3 (Infinite execution keeps its meaning).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.infinite_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.infinite_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive H and arbitrary J, Tick J, tau and block sequence, if every E(n) lies strictly between -H and H, both the completed-gap threshold time and the actual paid label time are infinite.

No default label is assigned to an infinite history. Each individual gap is finite, and the growing clock exhausts all finite bit prefixes.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.consecutive_block_event`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.infinite_prefix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths.stopped_prefix_payment`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable](CriticalRenewalTable.md)
