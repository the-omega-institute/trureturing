# Original rectangular-word occurrence

## Abstract

Original rectangular-word occurrence

**Definition 1.1 (Selected original labelled paths).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.LabelledRoute`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.LabelledRoute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite hidden state type H, an original stationary binary edge presentation theta and states h and r, a labelled route consists of a natural edge count n, n plus one hidden states, n emitted Boolean labels, endpoint equalities to h and r, and strict positivity of every selected original matrix entry. Its probability weight is pathMass of these states and labels. The empty path has weight one. This structure contains no desired occurrence probability or erasure inequality.

**Definition 1.2 (One visible event for the whole original block).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.success`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.success` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a binary list w and natural block length b, success is the set of future output sequences whose first b emitted bits, in their original order, contain the complete list w as an infix. This is the same event used by originalSuccessCount for one block. The hidden starting state does not enter the event, and multiple overlapping appearances pay only one success.

**Definition 1.3 (The exact selected-path minimum).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.selectedEpsilon`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.selectedEpsilon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For theta, w, a target state r, and one selected labelled route from every h to r, epsilon is the minimum over all h in H of the selected pathMass multiplied by the row sum at r of the original word matrix product. The index set is nonempty because it contains r. The minimum retains the particular selected labels and paths; it is not replaced by an optimized route, a power of the unlabelled transition matrix, or a positive surrogate.

**Theorem 1.4 (The original visible event is paid against the complete marked past).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.original_rectangle_occurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.original_rectangle_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any finite hidden state type with measurable singletons, theta an original stationary nonnegative binary edge presentation satisfying its scalar no11 condition, and J any probability measure with exactly theta's original integer-time marked cylinder identities. Let w have a nonempty rectangular positive word-matrix support, let r belong to its support rows, and select one positive original labelled route from every h to r, each with at most card(H) edges. Set b to length(w) plus card(H), and epsilon to the exact selected-path minimum. Then epsilon is strictly positive and at most one. At every integer cut t and every state h with positive theta initial mass, the actual conditional future kernel futureLaw(J,t,h) assigns success(w,b) probability at least epsilon. For every h, including a null hidden fiber, and every measurable event A of the entire marked past, epsilon times J of state(t)=h and past(t) in A is at most J of that same event together with future(t) in success(w,b). Measures and the inequality use ENNReal.ofReal(epsilon). The path followed by w fits inside the original b-bit block and is a subset of this single visible success event; summing hidden paths gives its lower probability. The complete-past factor is the existing same-law future-screening theorem. A null state has zero past-event mass. No independence, aperiodicity, unifilarity, global matrix positivity, posterior band or conditioning on future data is imposed. This is the occurrence-probability prerequisite of source Theorem 4.2. It does not construct the source's bounded routes from irreducibility or prove adapted success-count payment, either complete-half-line erasure bound, or the root and squared tails. Those are still required before the original theorem or its Section 7 loss-cocycle and second-order localization consumers can be closed.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.LabelledRoute`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.original_rectangle_occurrence`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.selectedEpsilon`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.success`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening](OriginalFutureScreening.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleSmoothing](OriginalRectangleSmoothing.md)
