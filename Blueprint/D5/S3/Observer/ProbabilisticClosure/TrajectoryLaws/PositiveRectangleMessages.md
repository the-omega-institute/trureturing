# Uniform guards from positive rectangular support

## Abstract

Uniform guards from positive rectangular support

**Definition 1.1 (The protected matrix mass with farther messages).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.sandwich`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.sandwich` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite rectangular matrix T from I to J, a middle matrix B from J to I, and arbitrary messages alpha on I and beta on J, sandwich is the sum over j,i of (sum_k alpha(k)T(k,j)) B(j,i) (sum_l T(i,l)beta(l)). It is the scalar alpha T B T beta.

**Theorem 1.2 (Every nonnegative farther message shares one strict guard).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.uniform_posterior_guard`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.uniform_posterior_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonempty finite I,J, strictly positive T, and two entrywise nonnegative middle matrices with strictly positive total masses, there exists one epsilon with 0<epsilon<=1/4 such that every pair of nonnegative farther messages with positive total protected mass gives a center-one ratio between epsilon and 1-epsilon. The same epsilon works for every farther row and column. Positive finite entry minima and finite upper bounds control both copies of T. There is no rank-one assumption and no normalization of zero-total atoms.

**Definition 1.3 (Exact positive rectangular support).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.Rectangle`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.Rectangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Rectangle(T) carries nonempty finite row and column supports, strictly positive entries at every included pair, and zero entries outside their Cartesian product. It imposes no restriction on rank.

**Theorem 1.4 (A guard on the original state coordinates).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.supported_message_guard`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.supported_message_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite original state type, exact Rectangle(T), two nonnegative middle matrices, and a common nonnegative initial row giving positive protected masses for both center symbols, one epsilon in (0,1/4] bounds the center posterior away from zero and one for every nonnegative farther row and column with positive total mass. The proof restricts all sums exactly to the declared support subtypes, obtains positive middle support sums from the actual protected masses, and applies uniform_posterior_guard. All original outside-support zeros remain in the full scalar formula.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.Rectangle`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.sandwich`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.supported_message_guard`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.uniform_posterior_guard`
