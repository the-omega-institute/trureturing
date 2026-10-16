# Recovery of the original future residue

## Abstract

Recovery of the original future residue

**Definition 1.1 (Only the time-one residue).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueTarget`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

residueTarget(z) is the index modulo three of the original hidden state H1. Its target omits the initial F/T phase.

**Definition 1.2 (The actual future prefix).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.futureWord`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.futureWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

futureWord(r,z) reads exactly the original emitted coordinates one through r from the same original hidden/output realization.

**Definition 1.3 (The same-law initial-residue MAP choice).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueMAP`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueMAP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural r, residueMAP is the existing fixed-order actual cell-mass maximizer for residueTarget and futureWord(r) under the original J. All words, ties and zero-mass observations remain in its total domain.

**Theorem 1.4 (Summable errors recover Z1).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.actual_future_residue_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.actual_future_residue_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On exactly the original J, every initial-residue MAP error at length r is at most ofReal((11/2)*rho^(r/2)), and these estimates are almost surely eventually equal to Z1. The source conclusion requires measurability of Z1; this proof uses a summable coefficient obtained before merging the twelve original hidden lifts. Actual state/future cylinder masses feed the actual MAP estimate. Their word probabilities factor through the six original phase/residue labels. Distinct initial residues remain distinct under every common word, so full affinity for such a pair equals its killed-pair survival affinity. The actual two-step affinity and specified_survival give the same rho=sqrt(15)/4. The proof does not infer an initial F/T phase decoder.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.actual_future_residue_recovery`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.futureWord`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueMAP`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueTarget`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery](FixedTargetRecovery.md)
