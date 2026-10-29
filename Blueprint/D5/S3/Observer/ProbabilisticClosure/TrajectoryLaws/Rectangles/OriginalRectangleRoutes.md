# Simple original routes to a rectangular word

## Abstract

Simple original routes to a rectangular word

**Theorem 1.1 (Irreducibility pays the visible word occurrence on the original law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.irreducible_rectangle_occurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.irreducible_rectangle_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any finite measurable hidden state type with measurable singletons, theta a stationary nonnegative binary edge presentation with its original scalar no11 condition, and J a probability measure with exactly theta's original integer-time marked cylinders. Assume irreducibility in the form that every pair of states has a positive entry in some nonnegative natural power of M0 plus M1. Let w be a binary list with nonempty rectangular positive matrix support, and r a support row. There exists a selected positive original labelled route from every h to r, with an injective list of hidden vertices. The route from r is empty and has weight one. Every route has at most card(H) edges; when the word begins with zero, every route has strictly fewer than card(H) edges. If the word begins with one and h differs from r, the last selected edge is labelled zero. For precisely these selected routes, epsilon is their exact minimum pathMass multiplied by the row sum of the original word product at r, and b is length(w) plus card(H). Epsilon is strictly positive and at most one. At every integer cut and every positive hidden fiber, the actual conditional future kernel assigns the one common visible success(w,b) event probability at least epsilon. For every hidden state, including a null fiber, and every measurable event A of the entire marked past, ENNReal.ofReal(epsilon) times J of state=h and past in A is at most J of that event together with future in success(w,b). The selected routes, visible event and conditional probabilities all belong to this same original J.

The route construction directly reuses the pinned shortestPath and shortest_path_spec APIs and the existing quiver isStrictlySimple_of_shortest and simple-path cardinality theorems. The original matrix-power support API supplies reachability, while label extraction preserves the complete vertex list. Simplicity therefore survives the assignment of positive original Boolean emission labels. For a word beginning with one, positivity of its support row gives a positive one-labelled outgoing edge at r. Original scalar no11, applied through positive-state trimming and the irreducible stationary masses, makes every one-labelled incoming entry at r zero. The final edge of a nonempty positive simple route into r is consequently labelled zero, with no appended detour. Injectivity makes the route from r empty. The same incoming-zero property also excludes a just-emitted one on an actual past arriving at r in the empty-prefix case. For a word beginning with zero, no incoming-label restriction is needed. The occurrence estimate directly reuses original_rectangle_occurrence with precisely these selected routes and their exact selectedEpsilon. It is a prerequisite of source Theorem 4.2, and does not assert either full-half-line erasure inequality, adapted success-count payment, or any root or squared-tail constant. Source Section 7 still requires those full bounds for its loss-cocycle and second-order localization applications.

**Theorem 1.2 (The empty-prefix incoming-past seam is null).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.first_one_incoming_past_null`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.first_one_incoming_past_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any finite measurable hidden type with measurable singletons, theta an original stationary nonnegative binary edge presentation satisfying only its scalar no11 condition, and J any probability with theta's original marked cylinders. Assume every pair of states has a positive entry in some natural power of M0 plus M1. For any rectangle word w beginning with one, any positive support row r, and every integer cut d, J of the event H(d)=r and X(d-1)=one is zero. Irreducible stationary masses are positive, and the existing scalar-no11 trimming argument gives zero for every incoming one-labelled entry at r. The forbidden event is contained in the finite union of original one-edge cylinders ending at r with label one; each has exactly zero original cylinder mass. This proves a statement about actual past trajectories, rather than just a matrix-entry statement.

For an actual positive-weight source class C, apply this result to nativeComponent with its unchanged original matrix entries and actual original-cylinder law K. Inclusion sends the null statement to the identical event on the original H/output carrier of J_C. The indicator of that event is almost everywhere zero, so its conditional expectation on the complete original marked-past sigma-field is zero as well. For the given empty route a(r), length zero gives pathMass exactly one. Thus a source word beginning with one has no positive-mass incoming-past conflict at the empty-prefix seam. Stationarity, positivity of the mass at r and the incoming-one zeros also give a positive zero-labelled predecessor; a simple route ending at r has a final zero edge. All conclusions stay inside the actual positive class. No global entrywise M1-squared-zero hypothesis is added.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.first_one_incoming_past_null`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes.irreducible_rectangle_occurrence`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Combinatorics/Quiver/Path](../../../../Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Combinatorics/Quiver/Path.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleOccurrence](OriginalRectangleOccurrence.md)
