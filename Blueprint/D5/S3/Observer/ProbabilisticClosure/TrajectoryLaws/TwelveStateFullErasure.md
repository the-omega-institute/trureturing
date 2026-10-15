# Actual half-line recovery and full erasure

## Abstract

Actual half-line recovery and full erasure

**Theorem 1.1 (A measurable decoder from finite-target stabilization).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.measurable_eventual_decoder`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.measurable_eventual_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sequence of measurable maps into a nonempty finite measurable target, there is one measurable decoder agreeing with every eventual constant value. The exact existing construction is consumed by the actual half-line decoders and invariant-event half-line approximation.

**Theorem 1.2 (The actual emitted-bit edge relation).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the original J, H1=next(H0,X0) almost surely. Impossible marked cells have zero original cylinder mass. The unchanged edge supplier is consumed by full erased-bit recovery and by the stationary predecessor-phase identity in the exact forcing contribution proof.

**Theorem 1.3 (Joint measurable half-line decoders).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_halfline_decoders`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_halfline_decoders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist measurable maps gL from the complete Boolean past to the six labels and gR from the complete Boolean future to Fin 3 such that gL(before(outputs))=Q0 and gR(after(outputs))=Z1 jointly almost surely under the original J. The proof constructs measurable eventual-value decoders for the same-law summable MAP estimates. It recovers no initial future phase.

**Theorem 1.4 (The actual full posterior equals X0).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_full_erasure`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_full_erasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original visible P, fullMean(parameter) equals erasedBit almost surely. Both the integral of fullMean times one minus fullMean, and the full squared prediction loss integral, equal zero. The original marked cylinder law gives the actual edge rule almost surely. The past decoder gives the residue at zero, the future decoder gives the residue at one, and the original zero/one increments distinguish X0. The resulting exterior-measurable bit version is identified with the actual full conditional expectation through visible_conditional_pullback, then transferred along the actual visible pushforward. These are actual-law conditional quantities, not a posterior table.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_edge`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_full_erasure`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.actual_halfline_decoders`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFullErasure.measurable_eventual_decoder`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery](TwelveStateFutureRecovery.md)
