# Original joint stochastic execution

## Abstract

Finite stochastic joint operations and their common fresh table realization.

**Theorem 1.1 (The entire finite joint execution law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.finite_execution_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.finite_execution_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite complete configuration carrier C with measurable singletons, an emission tag, and two configurations carrying its two Boolean decisions. An original stochastic specification gives a joint initialization distribution and, for every complete configuration and acquired bit, a joint distribution of the intermediate configuration and ensuing action. A read action carries a none-tagged complete configuration; an emitted action carries a configuration with its own decision tag. These original joint distributions are specified without any innovation tape, and can correlate the update and action choice.

One fresh innovation is a finite table with one joint outcome for every configuration and bit. Its distribution is the product of all original operation rows. The machine evaluates only the entry indexed by its actual complete configuration and newly read bit. Initialization samples the original joint initialization law. The table and initialization outcome are source independent. Neither table, source name, clock, acquired receipt nor unused random choices are retained in C.

For every fixed source bit sequence and every natural allowance n, the original joint execution distribution is defined recursively by the original initialization and operation rows. Its vector records n+1 successive joint outcomes. After internal emission its previous outcome is held, with no read or operation. The table interpreter on an independent seed and n independent fresh tables has exactly this entire vector distribution. The statement retains both intermediate configurations and their correlated ensuing actions, and includes initial emission, arbitrary terminal configurations, null paths and allowance zero. It is an equality of measures on the complete finite trace space, not only of one-operation marginals.

The induction separates the last fresh table from the preceding seed and tables. It transports the complete preceding trace distribution and integrates the selected original joint row. The finite table is an analytical representation of fresh randomness, not an accessible persistent random tape. The same original stochastic specification serves both source labels. The common realization also transports this finite representation to the independent infinite innovation product and identifies its actual actions with the original execution. No entropy, occupation or full E4 conclusion is asserted by the finite execution identity.

**Theorem 1.2 (One common realization of the original experiment).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.original_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.original_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any original stochastic observer on a finite complete C with card(C)<=M, its two internal emitted labels, and one common q strictly between zero and one. There exist common initialization and zero/one rows on the read-ready boundary, with at most M states and the two decisions absorbing. Neither these rows nor the initialization or fresh-table measure depends on the true source label.

For either literal original renewal source, the sample consists of the initial wait and infinite gap sequence, independently paired with the original initialization seed and infinite independent innovation tables. The source PMFs are exactly OriginalRenewalLaws.waitLaw and gapLaw for that same q, including the stationary wait at zero and the K+1 intertick convention. On every deterministic source sequence the entire finite table execution law is the original recursive joint law. For arbitrary measurable source and full-trace events, the joint cylinder mass is the integral of this original recursive law over the original source event. On each renewal realization, every action in the finite vector agrees pointwise with the original execute function. The cylinder with first emission at n and stopped receipt equal to the consecutive n-bit source prefix with internal decision d has exactly the mass assigned by the original finite law, including n=0 and null events.

The deterministic-coordinate Primitive identity holds on this very product for every source slice, every natural prefix length and following-block length, and arbitrary measurable prefix and block events. The seed and past innovation block have their joint product law, the next block is independent, and the source-slice mass has its exact first-wait and gap factors. Zero lengths and zero-mass slices are included without conditioning or division.

Applying the actual-history results to these same projections gives the joint source/state cylinders, every finite state prefix including the empty one, and the ordinary-past row identity for arbitrary measurable history and state events. The pointwise stopping normalization identifies the original stopIndex, paidCost, decision and stopped bit receipt with this same read-ready execution. Its tick stopping index N obeys N<=paidTicks<=T and N=0 exactly when T<=wait+1. Initial emission, stopping within a zero segment and nonemission retain their original meanings. No termination, finite-mean, entropy or E4 assertion is added.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.finite_execution_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.original_realization`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw](ActualRenewalHistoryLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization](OriginalObserverNormalization.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws](OriginalRenewalLaws.md)
