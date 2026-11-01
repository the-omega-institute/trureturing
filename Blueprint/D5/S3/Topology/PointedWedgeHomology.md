# Open saturated subwedges and singular homology

## Abstract

Based open contractions yield the actual singular homology of a binary quotient wedge.

**Definition 1.1 (A saturated subwedge).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.part`

*Formalization.* `D5/S3/Topology/PointedWedgeHomology.part` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given pointed topological spaces (X,a),(Y,b), and subsets A,B containing their respective basepoints, part is the subset of the literal FiniteConeUnionWedge.Wedge quotient represented by A sum B. Membership descends because the complete pair of identified basepoints lies in those pieces.

**Theorem 1.2 (Open pieces give an open saturated subwedge).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.isOpen_part`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/PointedWedgeHomology.isOpen_part` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A and B are open, their saturated part is open in the actual quotient topology. The proof uses the quotient-map characterization of open subsets and the disjoint-sum topology.

**Definition 1.3 (The subspace is the quotient wedge of the pieces).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.partHomeomorph`

*Formalization.* `D5/S3/Topology/PointedWedgeHomology.partHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For open A,B containing a,b, the wedge of the subtype basepoints in A and B is homeomorphic to part. The raw subtype-sum homeomorphism, the restricted open quotient map and equality of the complete quotient kernels construct this homeomorphism. All equal, distinct and cross-summand representatives are included.

**Definition 1.4 (Collapsing a based contractible right summand).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.leftEquiv`

*Formalization.* `D5/S3/Topology/PointedWedgeHomology.leftEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual homotopy of the identity on Y to the constant b map, relative to b, gives Wedge(a,b) homotopy equivalent to X. The maps are the left projection and left inclusion. Their inverse homotopy reuses the genuine private FiniteConeUnionWedge.wedgeInverseHomotopy and wedgeMap through Batteries.OpenPrivate. That supplier descends the cylinder homotopy continuously by continuous_lift_prod_right and local compactness of the unit interval; no unproved quotient-cylinder continuity premise is added.

**Definition 1.5 (Collapsing a based contractible left summand).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.rightEquiv`

*Formalization.* `D5/S3/Topology/PointedWedgeHomology.rightEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual quotient-swap homeomorphism followed by leftEquiv gives equivalence to Y whenever the contraction of X fixes a.

**Theorem 1.6 (Two based contractions contract the quotient wedge).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.contractible_wedge`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/PointedWedgeHomology.contractible_wedge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both summands have identity-to-basepoint homotopies fixing their basepoints, the actual wedge is contractible. The proof transports the contraction through leftEquiv and is used for the intersection of the open cover.

**Definition 1.7 (Positive-degree homology of the actual quotient wedge).**

Lean statement: `D5/S3/Topology/PointedWedgeHomology.homologyIso`

*Formalization.* `D5/S3/Topology/PointedWedgeHomology.homologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Suppose a and b have open neighborhoods A and B with the supplied contractions relative to those basepoints. For every q>0 and coefficient object in an abelian category with the required coproducts, H_q(X;R) biproduct H_q(Y;R) is isomorphic to H_q(Wedge(a,b);R). The saturated open subsets X wedge B and A wedge Y cover the quotient. They are homotopy equivalent to X and Y, and their intersection is homeomorphic to A wedge B and contractible. OpenCoverHomology.inclusionIso supplies the actual open Mayer–Vietoris split, including the reduced-H_0 argument for q=1. Positive reduced and ordinary homology are definitionally equal in the existing TauCeti port. The open-cover method is classical; these source-bound quotient and homotopy constructions are local implementation content.

## References

- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.contractible_wedge`
- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.homologyIso`
- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.isOpen_part`
- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.leftEquiv`
- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.part`
- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.partHomeomorph`
- Truth anchor: `D5/S3/Topology/PointedWedgeHomology.rightEquiv`
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](../Geometry/FiniteConeUnionWedge.md)
- Dependency: [D5/S3/Topology/OpenCoverHomology](OpenCoverHomology.md)
