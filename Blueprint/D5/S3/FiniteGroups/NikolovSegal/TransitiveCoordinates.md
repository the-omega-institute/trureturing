# Actual cycle coordinates and Hall interval selection

## Abstract

Finite Hall choices and minimal-period correction laws supply supported ordered coordinate products from an explicit scalar PRODUCT input.

**Definition 1.1 (qPowerGraph).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerGraph`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite generator tuple sigma on an index type I and a natural q, two distinct vertices are adjacent precisely when some sigma(j) to the q power sends one to the other. Generator labels are retained when an edge is selected. Original transitivity does not imply connectivity after powering.

**Theorem 1.2 (qPowerGraph spanningForest).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerGraph_spanningForest`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerGraph_spanningForest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite index type, the actual q-powered graph has an acyclic subgraph with exactly the same reachability relation. This applies separately to every powered component.

**Theorem 1.3 (qPowerForestEdgeLabel).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerForestEdgeLabel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerForestEdgeLabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge of a subgraph of the actual q-powered graph comes from a generator j and one of the two displayed orientations. This gives an actual labelled permutation arc rather than an invented edge map.

**Definition 1.4 (PartIIScalarProductInput).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.PartIIScalarProductInput`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.PartIIScalarProductInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a group S, natural q and M, component automorphisms beta and lengths e indexed by Fin M, the input says: if each e is positive and divides q, there exists a correction tuple x such that for every target t in S there exists c with the increasing ordered product of c(j) inverse times the action of (beta(j) times conj(x(j)) inverse) to the power q divided by e(j) on c(j) equal to t. Corrections precede all targets. This is an explicit scalar PRODUCT premise; its uniform finite-simple existence is unproved here.

**Definition 1.5 (cycleComponent).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.cycleComponent`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.cycleComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting at i, compose the actual component automorphisms along successive sigma(j) iterates. The zero-step component is the identity and the successor rule retains composition order.

**Theorem 1.6 (actual cycle component action).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_cycle_component_action`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_cycle_component_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If k(j)(z)(sigma(j)(i)) equals beta(j)(i)(z(i)) for every coordinate, the n-fold action evaluated at the n-th iterate of i equals the accumulated cycle component applied to z(i). This holds for arbitrary n and arbitrary groups.

**Definition 1.7 (correctedCycleComponent).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.correctedCycleComponent`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.correctedCycleComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Accumulate the component automorphisms after the fixed inner corrections y along the actual permutation path. The correction at each source coordinate is used in the same order as the corrected action.

**Theorem 1.8 (actual corrected cycle component action).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_corrected_cycle_component_action`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_corrected_cycle_component_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the genuine coordinate law, n iterations of k(j) times conj(y(j)) inverse at the n-th permutation iterate equal correctedCycleComponent applied to the initial coordinate. The tuple y is fixed throughout.

**Theorem 1.9 (actual corrected q power coordinate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_corrected_q_power_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_corrected_q_power_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the corrected coordinate law to the exact exponent q. The permutation coordinate is sigma(j) to the q power and the component is the q-step correctedCycleComponent. No inverse relation between different arcs is imposed.

**Theorem 1.10 (actual cycle component at return).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_cycle_component_at_return`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_cycle_component_at_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the permutation returns to its starting coordinate after e steps, the e-step accumulated component gives the corresponding return action. This supplies the actual component law used in the correction construction.

**Theorem 1.11 (actual factor tuple corrections).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_corrections`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_corrections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the explicit injective representative map, selected-index family, positive returning minimal cycle lengths and independence hypotheses, a scalar correction family can be extended to one tuple y on all factor coordinates. The resulting corrected return action agrees with each prescribed scalar correction, simultaneously across representatives.

**Theorem 1.12 (actual factor tuple q power corrections).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_q_power_corrections`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_q_power_corrections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each selected cycle whose positive length e divides q, the single correction tuple realizes the corrected scalar return component to the exact power q divided by e. The hypotheses retain return, minimality and simultaneous cycle independence.

**Theorem 1.13 (actual factor tuple q power from coordinate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_q_power_from_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_q_power_from_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting from the genuine k, sigma and beta coordinate law and the supplied selected cycle data, construct one global y realizing the scalar corrected q divided by e action at all selected representatives. The chosen scalar corrections and divisibility assumptions are explicit.

**Theorem 1.14 (actual selected supported ordered product reconstruction with support).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_selected_supported_ordered_product_reconstruction_with_support`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_selected_supported_ordered_product_reconstruction_with_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume an injective finite representative map, exactly M selected indices per representative, positive selected lengths dividing q, actual returns, minimality and independence of selected cycles, together with the corresponding Part-II scalar PRODUCT inputs. Construct one tuple y before every representative and every scalar target. The target-dependent tuple c has ordered corrected q-powered product supported only at that representative, and c itself is one outside the selected indices and that representative. Increasing selected-index embeddings preserve the noncommutative generator order.

**Theorem 1.15 (actual selected interval with support).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_selected_interval_with_support`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_selected_interval_with_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q, D and M with M times D times (q plus D) at most m, injective representatives, good q-periodicity, fewer than D bad indices per representative and the actual coordinate law, assume the scalar PRODUCT input for every qualifying M-index selection. Construct consecutive good prefix pieces, selected M-index sets and one global correction tuple y. For every representative and target, a supported c realizes exactly that one-coordinate target, with c one outside the selected support. Minimal periods provide positive e dividing q and the exact q divided by e exponent.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Lemma 10.3 and equations (45)-(50), printed pages 228-231. The scalar PRODUCT premise is the input of Part II, Theorem 1.2, equivalent to Part I, Theorem 1.10; Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. These are adaptations and proofs of conditional consequences of published mathematics, with no originality claim. Uniform scalar existence, genuine type-II reconstruction, mixed representative bounds, uniform width, restricted Burnside bounds and unconditional strong completeness remain unproved.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.PartIIScalarProductInput`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_corrected_cycle_component_action`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_corrected_q_power_coordinate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_cycle_component_action`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_cycle_component_at_return`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_corrections`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_q_power_corrections`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_factor_tuple_q_power_from_coordinate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_selected_interval_with_support`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.actual_selected_supported_ordered_product_reconstruction_with_support`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.correctedCycleComponent`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.cycleComponent`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerForestEdgeLabel`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerGraph`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates.qPowerGraph_spanningForest`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TransitiveHall](TransitiveHall.md)
