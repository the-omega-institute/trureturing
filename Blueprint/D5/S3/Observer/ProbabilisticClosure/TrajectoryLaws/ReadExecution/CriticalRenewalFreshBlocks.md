# Critical renewal FreshBlocks

## Abstract

A mark from its own actual gap.

**Theorem 1.1 (A mark from its own actual gap).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.block_pair_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.block_pair_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural J, any duration mass function f and immutable Tick J, the pushforward of blockLaw f t under b mapped to (length(b.zeros),increment(t,b)) is exactly pairLaw f t.

zeroTraceLaw starts with the empty zero history and phase zero. At each successive zero it samples the capped phase coin at the current phase and appends the outcome, retaining the terminal phase as a proof coordinate. markedTraceLaw then samples the one tick coin at that phase. The resulting Block contains only the finite zero outcomes and its tick outcome; its duration is the length of that very history.

The support induction identifies both the trace length and terminal phase, and the marginal phase induction gives GeometricPhaseOccupation.finiteCappedLaw. Thus the potential pair is the duration and mark of these same coins, with no independence claim inside a pair.

**Theorem 1.2 (Independent blocks on the same renewal source).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.fresh_same_source`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.fresh_same_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any initial-wait mass function w, duration mass function f and immutable Tick J, sourceLaw is w times the infinite product of the freshly constructed block laws. The duration-mark pairs extracted from successive coordinates are mutually independent, and every one has exactly pairLaw f t. The complete pair sequence is independent of the initial wait. The pushforward retaining only the initial wait and all actual durations is exactly w times the infinite product of f. For every positive H and interior evidence e, the distribution of target(e+increment) from a sampled block equals the f-mixture of the literal k-zero/one-tick word laws.

The numerical equilibrium wait law and the two polynomial-exponential duration laws may be inserted into w and f separately. The table remains unchanged between source labels. The construction does not assume or assert independence of a gap duration and its own terminal score.

The pathwise execution uses the initial wait and this one block sequence in chronological order. The proof arrays, block indices, phase histories and clocks do not enlarge State H J.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.block_pair_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks.fresh_same_source`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths](CriticalRenewalPaths.md)
