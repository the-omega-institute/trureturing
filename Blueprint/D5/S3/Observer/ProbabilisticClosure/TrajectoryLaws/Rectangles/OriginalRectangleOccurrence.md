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

**Definition 1.5 (The prescribed original hidden path and word).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.routeWord`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.routeWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an original presentation theta, any integer cut t, states h and r, a given positive labelled route a from h to r, and a Boolean list w, routeWord is the intersection of the original marked cylinder prescribing exactly a's hidden states and labels with the visible w cylinder beginning at t plus a.length. It restricts no coordinate after that word. In particular, the selected family is supplied as data; this event does not choose a new route or change the source epsilon.

**Theorem 1.6 (Exact prescribed-route probability against the entire marked past).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.route_word_past_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.route_word_past_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite measurable hidden type with measurable singletons, every original presentation theta, every probability J with theta's original integer-time marked cylinders, every integer t, states h and r, given positive labelled route a from h to r, and Boolean word w, routeWord is measurable. For every natural b with a.length plus length(w) at most b, this particular hidden event is contained in future(t) in the same success(w,b) visible event. For every measurable set A of the entire infinite marked-past sequence, J(past(t) in A and routeWord) equals J(H(t)=h and past(t) in A) multiplied by ENNReal.ofReal of pathMass(theta.matrix,a) times the row sum at r of product(theta,w). This is an equality, including null hidden or past fibers. There is no additional conditional Markov hypothesis and no conditioning on future observations. The finite-cylinder calculation concatenates the prescribed past and route, reuses the original path-product concatenation, and applies past_future_mass only after the prescribed route. Equality of all finite projections then identifies finite measures on the complete marked-past sequence, giving the displayed factorization for arbitrary measurable A. The visible-event inclusion uses the original emitted coordinates of the prescribed route followed by w.

**Definition 1.7 (The actual positive closed-class restriction).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.nativeComponent`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.nativeComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an actual closed communicating class C of the original sum matrix M0 plus M1, let c be the sum of the original stationary masses over C and assume c is positive. The restricted presentation has hidden type exactly the original subtype C, stationary mass lambda(h)/c, and matrices Mx(h,k) with their original real entries. Closedness supplies the restricted row sums. Original stationarity and equality of the total stationary mass entering and leaving C give restricted stationarity. PositiveSupportPresentation.weighted_no11 supplies the original two-one matrix entry from every state with positive original initial mass. For a zero-mass state the corresponding weighted product is zero directly. Restricting this weighted identity and dividing by c gives the scalar no11 field of nativeComponent; no entrywise condition is added to the original parameter domain. Neither the original hidden index type nor the emission clock is renumbered.

**Definition 1.8 (Inclusion on the same original marked carrier).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.componentInclusion`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.componentInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path on the actual state subtype C is included in the original path space by taking the value of each hidden subtype coordinate. Every integer output coordinate is unchanged.

**Theorem 1.9 (A native component law equals the actual class restriction).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.component_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.component_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let theta be the original stationary edge presentation on finite H. Let C be an actual closed communicating class of theta's sum matrix, let c be its positive original stationary mass, and let kappa be nativeComponent(theta,C,c-positive), with exactly the original subtype, normalized masses and unchanged matrix entries. Let J and K be probability measures with the original marked cylinders of theta and kappa respectively. For every integer t, c times the inclusion pushforward of K equals the restriction of J to the event H_t belongs to C. For every word, the product of the restricted matrices is also exactly the restriction of the original word product. Restricted stochasticity forces every omitted outgoing entry to be zero, and induction through matrix multiplication preserves each original entry. The assumptions themselves force c to be the actual stationary mass of C. The result holds for every such J and K, including reducible or periodic presentations and zero-mass states. It identifies measures on the original hidden/output carrier, rather than identifying only visible marginals or assigning an original-law name to an unrelated supplied measure. The proof first compares all original marked cylinders, extends the comparison to all measurable events by finite-window approximation, and then uses support in C and equality of total mass to obtain the restriction identity. For nativeComponent, the initial-mass and matrix equalities follow from its defining original entries, so the normalized restriction of J is precisely K's inclusion pushforward at every integer cut. Its output marginal is consequently the same actual class-conditioned visible law.

To apply the occurrence estimate to a positive-weight source class, take H in original_rectangle_occurrence to be exactly C, theta to be nativeComponent of the original parameter and class, and K to be the original-cylinder law of that restricted presentation. The preceding measure identity identifies its inclusion with the normalized restriction of the original J; it is not a new probability model. Keep the source word w and support row r, and supply the very family a of original labelled paths selected in the statement. The source d_h is pathMass of a(h), its B_C row sum is the row sum of product(kappa,w), and the source epsilon is exactly selectedEpsilon(kappa,w,r,a). Thus b is exactly length(w) plus card(C), with the original emission coordinates. Applying original_rectangle_occurrence directly to these parameters gives the one common success event, every integer cut, and every measurable complete marked-past event. This application does not replace a by a bounded or optimized family. The adapted count moment, the complete opposite-half-line erasure risks, all count and tail endpoint cases, and the Section 7 consequences require their respective additional arguments.

On the original H/output carrier let mu be K pushed forward by componentInclusion. For every integer d, component_restriction identifies mu exactly with the inverse of ENNReal.ofReal(c) times J restricted to H(d) in C. Lift the given a(h) only by taking each hidden subtype value; keep its length and emitted labels. The preimage of its original routeWord event under inclusion is precisely the native routeWord event. Inclusion also pulls every measurable event of the complete original marked past back to the corresponding native event, preserving H(d). Hence route_word_past_factor gives the same equality on mu for every original measurable marked-past event. Conditional-expectation uniqueness on the sigma-field generated by the pair (H(d),past(d)) identifies the conditional expectation of this particular event's indicator with its exact original path weight times the B_C row sum, multiplied by the indicator of H(d)=h. On that hidden fiber the conditional probability is therefore exactly d_h times (B_C one)(r), almost everywhere. This sigma-field contains every H(i) for i at most d and every X(i) for i below d; it is not a finite observation window. The original restricted word-product identity gives the very B_C in the source, and taking the minimum over the unchanged supplied family gives precisely its epsilon.

Set b to length(w) plus card(C). For each given route the remaining length is b minus a.length minus length(w). Partitioning routeWord by all remaining original hidden-state tuples and output tuples gives its entire measure, also when the remaining length is zero. The arbitrary suffix thus contributes total conditional mass one; no suffix positivity or special continuation is imposed. The proved inclusion puts this hidden subevent inside the single source success(w,b) event, so its exact conditional probability is at least the unchanged selectedEpsilon. This establishes the source proof's prescribed-path payment paragraph. It does not establish the chronological product moment, either complete opposite-half-line posterior comparison, or the root and squared tail estimates.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.LabelledRoute`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.componentInclusion`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.component_restriction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.nativeComponent`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.original_rectangle_occurrence`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.routeWord`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.route_word_past_factor`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.selectedEpsilon`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleOccurrence.success`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses](FiniteClosedClasses.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureScreening](OriginalFutureScreening.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleSmoothing](OriginalRectangleSmoothing.md)
