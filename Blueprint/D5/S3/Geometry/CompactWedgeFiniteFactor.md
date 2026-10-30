# Compact finite-factor reduction

## Abstract

Compactness reduces arbitrary ordinary wedge coproduct models to actual finite selected families.

**Definition 1.1 (The collapsed subset).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.basePoints`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.basePoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a pointed family (Z_j,b_j), take the ordinary topological sum of an additional one-point space and the dependent coproduct of all Z_j. The collapsed subset consists of the additional point and every factor basepoint. The subsetSetoid relation from FiniteConeUnionWedge identifies precisely this subset.

**Definition 1.2 (The common basepoint).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.base`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FamilyWedge b is the quotient by the collapsed subset, with its quotient topology. Its distinguished point is the class of the additional point. In particular an empty index type gives a point, rather than an empty space.

**Definition 1.3 (Original factors map continuously into the quotient).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.point`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor map is the composition of its coproduct inclusion with the quotient projection. Each factor basepoint maps to the common basepoint.

**Definition 1.4 (Off-basepoint support).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.support`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support of K consists of indices j for which some z different from b_j has its quotient class in K. One-point factors therefore contribute no off-basepoint support. Finiteness of support does not imply finiteness of the original index type.

**Theorem 1.5 (Compact subsets meet finitely many factors away from the basepoint).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.compact_support`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/CompactWedgeFiniteFactor.compact_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary J and pointed T1 factors, every compact K in the ordinary quotient wedge has finite support. Choose one encountered nonbasepoint class p_j for each support index. These classes are distinct. For every subset E of the chosen indices, the full saturated inverse image of p(E) is empty in the additional point and has at most one point in each original factor. It is closed by T1 and the coproduct topology, so p(E) is closed by the quotient topology. If support is nonempty, the open sets complementary to p(support minus {j}) cover K. IsCompact.elim_finite_subcover gives a finite subcover, and p_j belongs only to the j-th member, forcing finite support. Empty support is immediate. No compact-subset-closed implication, Hausdorff assumption on K, closed quotient-map assumption, CW structure, or noncontractibility is used. This explicit classical compactness argument is presented as a repository derivation, without a claim of novelty or an exact literature attribution.

**Definition 1.6 (Inclusion of the genuine selected-family quotient).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.inclusionMap`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.inclusionMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite F, Subwedge b F is the ordinary wedge of the unchanged factors indexed by the subtype j in F. Its continuous inclusion is constructed by the coproduct and quotient universal properties, rather than by assuming agreement of quotient and subspace topologies. F may be empty.

**Definition 1.7 (Retraction to the selected quotient).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.retract`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.retract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain each selected factor and send every omitted factor constantly to the selected wedge basepoint. The factor maps descend continuously because all factor basepoints agree in the target. The retraction composed with inclusion is the identity. Inclusion composed with retraction fixes every subset whose off-basepoint support is contained in F.

**Definition 1.8 (Actual finite-factor data for a continuous map).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.FiniteFactor`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.FiniteFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source X maps continuously to Y, an arbitrary dependent coproduct of ordinary wedges. The data consist of a finite nonempty outer selection A0, a finite inner selection F_a for each retained a, and continuous maps from the concrete selected model M to Y and from Y to M. The maps satisfy r(i(m))=m and i(r(f(x)))=f(x). M is the dependent coproduct over A0 of the actual quotients of the selected original factors. An empty inner selection remains a point component.

**Definition 1.9 (Compactness constructs the finite model and both maps).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.finiteFactor`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.finiteFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every nonempty compact X, every continuous f:X to Y and arbitrary pointed T1 factor family, finiteFactor constructs FiniteFactor b f. The native IsCompact.sigma_exists_finite_sigma_eq theorem supplies finite outer support from the compact range of f. Each outer coproduct inclusion is a closed embedding; its preimage of that compact range is compact without a Hausdorff assumption. Apply compact_support in each retained block. Include the resulting selected subwedges in their original blocks. Retract retained blocks by their wedge retractions; send every omitted outer block constantly to one chosen retained basepoint. Continuity follows blockwise from continuous_sigma_iff. Compactness and f provide a retained block because X is nonempty. All retained point components are present, including blocks with empty inner support.

**Definition 1.10 (Both inverse homotopies for the actual finite model).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.finiteFactorHomotopyEquiv`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.finiteFactorHomotopyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given an actual ordinary homotopy equivalence e:X to Y with nonempty compact X, construct the finite model using its forward map f. Its forward and backward maps are r composed with f and g composed with i. The strict equality i r f=f identifies their source composite with g f, so the supplied source inverse homotopy applies. For the target composite use J(t,m)=r(H(t,i(m))), where H is the supplied homotopy from f g to id_Y. Its endpoint is r i=id_M. Product and composition continuity suffice, and H need not remain in M. This proves an actual homotopy equivalence to the specified finite selected-family quotient model, rather than finite domination alone. Standard pointed spheres of dimension zero are retained as genuine factors. Splitting zero-spheres and conversion to positive bouquets with isolated points are separate steps; no full open-question resolution is asserted.

**Definition 1.11 (The separate empty-source model).**

Lean statement: `D5/S3/Geometry/CompactWedgeFiniteFactor.emptySourceHomotopyEquiv`

*Formalization.* `D5/S3/Geometry/CompactWedgeFiniteFactor.emptySourceHomotopyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An empty source is homeomorphic, hence homotopy equivalent, to the selected model with empty outer selection. The nonempty outer conclusion of finiteFactor applies only to nonempty X.

## References

- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.FiniteFactor`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.base`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.basePoints`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.compact_support`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.emptySourceHomotopyEquiv`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.finiteFactor`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.finiteFactorHomotopyEquiv`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.inclusionMap`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.point`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.retract`
- Truth anchor: `D5/S3/Geometry/CompactWedgeFiniteFactor.support`
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](FiniteConeUnionWedge.md)
