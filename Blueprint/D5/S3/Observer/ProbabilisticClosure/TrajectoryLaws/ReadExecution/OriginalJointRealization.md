# Original joint stochastic execution

## Abstract

Finite stochastic joint operations and their common fresh table realization.

**Theorem 1.1 (One common realization of the original experiment).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.original_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.original_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any original stochastic observer on a finite complete C with card(C)<=M, its two internal emitted labels, and one common q strictly between zero and one. There exist common initialization and zero/one rows on the read-ready boundary, with at most M states and the two decisions absorbing. Neither these rows nor the initialization or fresh-table measure depends on the true source label.

For either literal original renewal source, the sample consists of the initial wait and infinite gap sequence, independently paired with the original initialization seed and infinite independent innovation tables. The source PMFs are exactly OriginalRenewalLaws.waitLaw and gapLaw for that same q, including the stationary wait at zero and the K+1 intertick convention. On every deterministic source sequence the entire finite table execution law is the original recursive joint law. For arbitrary measurable source and full-trace events, the joint cylinder mass is the integral of this original recursive law over the original source event. On each renewal realization, every action in the finite vector agrees pointwise with the original execute function. The cylinder with first emission at n and stopped receipt equal to the consecutive n-bit source prefix with internal decision d has exactly the mass assigned by the original finite law, including n=0 and null events.

The deterministic-coordinate Primitive identity holds on this very product for every source slice, every natural prefix length and following-block length, and arbitrary measurable prefix and block events. The seed and past innovation block have their joint product law, the next block is independent, and the source-slice mass has its exact first-wait and gap factors. Zero lengths and zero-mass slices are included without conditioning or division.

Applying the actual-history results to these same projections gives the joint source/state cylinders, every finite state prefix including the empty one, and the ordinary-past row identity for arbitrary measurable history and state events. The pointwise stopping normalization identifies the original stopIndex, paidCost, decision and stopped bit receipt with this same read-ready execution. Its tick stopping index N obeys N<=paidTicks<=T and N=0 exactly when T<=wait+1. Initial emission, stopping within a zero segment and nonemission retain their original meanings. No termination, finite-mean, entropy or E4 assertion is added.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.original_realization`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw](ActualRenewalHistoryLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization](OriginalObserverNormalization.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws](OriginalRenewalLaws.md)
