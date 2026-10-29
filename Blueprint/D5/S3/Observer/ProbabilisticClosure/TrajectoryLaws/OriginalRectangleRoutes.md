# Bounded original routes to a rectangular word

## Abstract

Bounded original routes to a rectangular word

**Theorem 1.1 (Irreducibility pays the visible word occurrence on the original law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleRoutes.irreducible_rectangle_occurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleRoutes.irreducible_rectangle_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any finite measurable hidden state type with measurable singletons, theta a stationary nonnegative binary edge presentation with its original scalar no11 condition, and J a probability measure with exactly theta's original integer-time marked cylinders. Assume irreducibility in the form that every pair of states has a positive entry in some nonnegative natural power of M0 plus M1. Let w be a binary list with nonempty rectangular positive matrix support, and r a support row. There exists a selected positive original labelled route from every h to r. The route from r is empty and has weight one. Every route has at most card(H) edges; when the word begins with zero, every route has strictly fewer than card(H) edges. If the word begins with one and h differs from r, the last selected edge is labelled zero. For precisely these selected routes, epsilon is their exact minimum pathMass multiplied by the row sum of the original word product at r, and b is length(w) plus card(H). Epsilon is strictly positive and at most one. At every integer cut and every positive hidden fiber, the actual conditional future kernel assigns the one common visible success(w,b) event probability at least epsilon. For every hidden state, including a null fiber, and every measurable event A of the entire marked past, ENNReal.ofReal(epsilon) times J of state=h and past in A is at most J of that event together with future in success(w,b). The selected routes, visible event and conditional probabilities all belong to this same original J.

The route construction directly uses the pinned Matrix.pow_apply_pos_iff_nonempty_path theorem to obtain a positive path of the original sum matrix, then extracts an original Boolean emission label on each edge and constructs its finite-coordinate labelled route. Cayley-Hamilton reduces a nonzero reachable matrix entry to a positive power of order below card(H), without any aperiodicity assumption. For a word beginning with one, positivity of its support row gives a positive one-labelled outgoing edge at r. Original scalar no11, applied through the existing positive-state trimming theorem and the irreducible stationary masses, excludes every positive one-labelled incoming edge at r. Stationarity supplies a positive zero-labelled incoming edge, which is appended to a short route. The occurrence estimate then directly reuses original_rectangle_occurrence with the exact routes just constructed. The theorem asserts bounded positive routes; it makes no assertion that their vertex lists are simple. It is a prerequisite of source Theorem 4.2, and does not assert either full-half-line erasure inequality, adapted success-count payment, or any root or squared-tail constant. Source Section 7 still requires those full bounds for its loss-cocycle and second-order localization applications.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleRoutes.irreducible_rectangle_occurrence`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence](OriginalRectangleOccurrence.md)
