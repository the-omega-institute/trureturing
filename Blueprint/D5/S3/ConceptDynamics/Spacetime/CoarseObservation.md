# Native Coarse Observation

## Abstract

Finite observations of native histories preserve exact signed fiber arithmetic.

**Definition 1.1 (Full current and selected fibers on every bin).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A bin map is defined on the entire current-event subtype of an actual three-dimensional history. The output consists of background and selected integer arrays on the whole finite bin type. Unhit bins and signed cancellation remain present. These arrays carry no new causal history, spatial positions or source trees.

**Theorem 1.2 (The background array sums to current charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_backgroundBins`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_backgroundBins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite fiber summation counts every current occurrence exactly once. An empty bin type is allowed when the current region is empty, even if the retained archive is nonempty.

**Theorem 1.3 (The selected array sums to the arithmetic readout).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_selectedBins`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_selectedBins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected array uses the existing signed contribution and actual selection. Its total is the same integer readout as that of the rich representation.

**Theorem 1.4 (Selection complement subtracts from the background array).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_complement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal event complement keeps the background array and replaces the selected array by background minus selected charge. Global balance alone does not make every background bin zero.

**Theorem 1.5 (Successive finite merging composes).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.pushforward_comp`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.pushforward_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer indicator summation proves composition for both arrays without injectivity or surjectivity assumptions on either merging map.

**Theorem 1.6 (Coarsening agrees with observing through the composite map).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_coarsen`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_coarsen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each composite bin is the signed sum of its constituent original bins. The bin map remains defined only on current events; archived noncurrent events receive no default bin.

**Theorem 1.7 (Tagged parallel bins retain the two arrays separately).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_tagged_charges`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_tagged_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual parallel archive tags both inputs. Its current and selected fibers copy the corresponding left and right fibers, even when the input archives use equal event names.

**Theorem 1.8 (Common parallel bins add the two arrays).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_common_charges`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_common_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Merging left and right tags into a shared bin type gives pointwise addition of both background and selected charges.

**Theorem 1.9 (Each generated bin fiber retains ordered parent occurrences).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.generated_selected_bin_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.generated_selected_bin_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected fiber in the new generated current is the image of the Cartesian product of the two input selected fibers. Equal sources and cancellation never identify distinct ordered parent pairs. Both old archives remain retained outside the new current.

**Theorem 1.10 (The actual generated product multiplies both bin arrays).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_bin_charges`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_bin_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the native generated charge through its ordered parent fibers yields the product of the corresponding background charges and of the corresponding selected charges.

**Theorem 1.11 (Arbitrary product-bin merging follows the native product).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_coarsened_charges`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_coarsened_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula first uses the actual generated product and its parent-bin fiber equation, then pushes both arrays through any map from the product bin type.

**Theorem 1.12 (A balanced two-event history has nonzero spatial and source bins).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.two_bin_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.two_bin_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two events have opposite signs, common time zero, empty causal order, distinct leaf sources and distinct first spatial coordinates. Both are current and only the positive event is selected. In positive/negative order the arrays are (1,-1), (1,0), and the complement (0,-1); the complement is not the negative selected array.

**Theorem 1.13 (Global balance does not force local bin balance).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.not_global_balance_forces_local_balance`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.not_global_balance_forces_local_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed universal claim is refuted by the stated actual two-event history. This establishes the finite-bin counterexample and the arithmetic formulas of Proposition 9; it asserts no continuous physics, whole-theory completion, or ZFC conservativity result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.generated_selected_bin_fiber`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.not_global_balance_forces_local_balance`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_coarsen`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.observe_complement`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_common_charges`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.parallel_tagged_charges`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_bin_charges`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.product_coarsened_charges`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.pushforward_comp`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_backgroundBins`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.sum_selectedBins`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/CoarseObservation.two_bin_counterexample`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/GeneratedProduct](GeneratedProduct.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives](IntegerRepresentatives.md)
- Dependency: [D5/S3/Entropy/Forgetting/PushforwardComposition](../../Entropy/Forgetting/PushforwardComposition.md)
