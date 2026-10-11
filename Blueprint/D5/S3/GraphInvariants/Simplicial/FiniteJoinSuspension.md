# Finite geometric joins and ordinary suspension

## Abstract

The geometric join with two isolated points is the ordinary suspension of a nonempty finite polyhedron.

**Definition 1.1 (The usual finite polyhedron).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.geometricCarrier`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.geometricCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V and precomplex K, place vertex i at the coordinate vector with coordinate one at i and zero elsewhere. The carrier is the union, over the nonempty faces of K, of their closed convex hulls in the real product indexed by V. A coordinate vector belongs exactly when all its coordinates are nonnegative, their sum is one, and its true nonzero support is a face of K. The coordinate equivalence from finitely supported functions to the finite product transports Mathlib's onFinsupp polyhedron and the sourced simplex characterization to this literal union.

**Definition 1.2 (The true nonzero support).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.support`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite vertex type V with decidable equality and a real coordinate vector x, support x consists exactly of the vertices i for which x at i is nonzero. Zero coordinates are omitted. For a point of the carrier, every vertex whose singleton is absent has coordinate zero and is omitted from its support.

**Theorem 1.3 (Membership by barycentric coordinates and true support).**

$$\forall V : Type, [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] \forall K : \operatorname{PreAbstractSimplicialComplex}(V), \forall x : V \to \mathbb{R}, x \in \operatorname{geometricCarrier}(K) \iff (\forall i : V, 0 \leq \operatorname{x}(i)) \land \sum_{i : V} \operatorname{x}(i) = 1 \land \operatorname{support}(x) \in K$$

*Proof.* Machine-checked in Lean as `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.mem_geometricCarrier_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Finite barycentric polyhedra and precomplex joins in TauCeti*. URL: <https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d>.

*Commentary.*

For every finite vertex type V with decidable equality, every precomplex K on V and every real coordinate vector x, membership in the literal union of closed face hulls is equivalent to coordinate nonnegativity, total coordinate sum one, and the true nonzero support being a face of K. No nonemptiness or full-vertex hypothesis is imposed: for an empty carrier both sides are false, and ghost coordinates must vanish. The finite coordinate equivalence transports the sourced finitely supported characterization. This criterion characterizes join coordinates and verifies the suspension coordinate map and its normalized base points.

**Definition 1.4 (The Euclidean subspace topology).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.GeometricRealization`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.GeometricRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization is the carrier with the subspace topology from the finite real product. It is compact, since each closed face simplex is compact and there are finitely many faces. It is Hausdorff as a subspace of that real product. A vertex whose singleton is absent contributes no points to the carrier.

**Definition 1.5 (The disjoint vertex join).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.join`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.join` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Finite barycentric polyhedra and precomplex joins in TauCeti*. URL: <https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d>.

*Commentary.*

For arbitrary precomplexes K and L, a finite set of tagged vertices is a join face precisely when it is nonempty and each projection is either empty or a face of its factor. Empty contributions are allowed independently. The join and the coordinate-support characterizations follow TauCeti at revision 64bb4d871548995899dee90beda88b787fafe27d, in Join/Basic and Realization/Basic and Realization/Coordinates.

**Definition 1.6 (The two-point factor).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.D2`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.D2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D2 is the bottom abstract simplicial complex on Fin two, regarded as a precomplex. Its faces are the two singletons; the edge is absent. Thus a point of the geometric join has at most one nonzero pole coordinate. Bottom as a precomplex instead has no faces and is a different object.

**Definition 1.7 (The closed height interval).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.Height`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.Height` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Height is the closed real interval from minus one to one, with its real subspace topology.

**Definition 1.8 (Collapse the endpoint fibres separately).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionSetoid`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every topological space X, take the cylinder of X with the closed real interval from minus one to one. Two cylinder points are related precisely when their heights agree and that common height is an endpoint or their base points agree. This equivalence relation is specified independently of any map into a geometric realization. Opposite endpoints have different heights and remain distinct whenever X is nonempty.

**Definition 1.9 (The ordinary unreduced suspension).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.OrdinarySuspension`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.OrdinarySuspension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary suspension of X is the quotient of that cylinder by the endpoint relation, with the quotient topology. If X is empty, the cylinder and its quotient are both empty.

**Definition 1.10 (The barycentric coordinate map).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionCoordinates`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a base point x and height s, give base vertex i coordinate (one minus the absolute value of s) times x at i. Give pole zero coordinate max of s and zero, and pole one coordinate max of minus s and zero. The coordinates are nonnegative and sum to one. The base support is either the support of x or empty, and at most one pole occurs, so the true support is a face of the join.

**Definition 1.11 (A continuous map into the actual join).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionMap`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate map takes every cylinder point to the literal Euclidean realization of the join. Absolute value, maximum and coordinate multiplication give continuity. No connectedness or requirement that every ambient vertex be used is imposed.

**Theorem 1.12 (The fibres are exactly the ordinary suspension relation).**

$$\forall V : Type, [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] \forall K : \operatorname{PreAbstractSimplicialComplex}(V), \forall p : \operatorname{Cylinder}(\operatorname{GeometricRealization}(K)), \forall q : \operatorname{Cylinder}(\operatorname{GeometricRealization}(K)), \operatorname{suspensionMap}(p) = \operatorname{suspensionMap}(q) \iff \operatorname{suspensionSetoid}(\operatorname{GeometricRealization}(K), p, q)$$

*Proof.* Machine-checked in Lean as `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionMap_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of pole coordinates recovers the common height as their difference. At either endpoint the remaining base mass is zero. Away from the endpoints it is strictly positive, and equality of scaled coordinates recovers the base point. Conversely, equivalent cylinder points have the same coordinates. This statement includes empty realizations without a nonemptiness hypothesis.

**Definition 1.13 (Descend to the endpoint quotient).**

Lean statement: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionQuotientMap`

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionQuotientMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact fibre identity allows the continuous cylinder map to descend to the ordinary suspension. The descended map is injective. For a join point with base coordinates z and pole masses a and b, set s to a minus b. One pole mass vanishes, so the absolute value of s is a plus b. If the remaining mass is positive, divide z by one minus the absolute value of s to obtain its unique base point. If that mass is zero, all base coordinates vanish and any existing base point maps to the required pure pole.

**Definition 1.14 (The finite geometric join is the ordinary suspension).**

$$\forall V : Type, [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] \forall K : \operatorname{PreAbstractSimplicialComplex}(V), \operatorname{Nonempty}(\operatorname{GeometricRealization}(K)) \Rightarrow \operatorname{Homeomorph}(\operatorname{GeometricRealization}(\operatorname{join}(K, \operatorname{Dtwo}())), \operatorname{OrdinarySuspension}(\operatorname{GeometricRealization}(K)))$$

*Formalization.* `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.joinSuspensionHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V, every precomplex K on V and a nonempty realization of K, the construction gives a Homeomorph from the geometric realization of the join with D2 to the ordinary suspension of K's realization. The inverse is the descended coordinate map. The cylinder quotient is compact; a continuous bijection from it to the Hausdorff join realization is a homeomorphism.

Nonemptiness is essential. For the empty precomplex, including on Fin zero, the realization and its cylinder quotient are empty, but its join with D2 has the two pure poles. No negative-dimensional sphere is introduced.

For path independence complexes at N at least one, this identifies the ordinary suspension once the exact relabelled deletion is the specified join. The exact path collapse and relabelling, its geometric homotopy equivalence, the path recurrence, the base cases and the full classification by residue modulo three are additional assertions.

## References

- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.D2`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.GeometricRealization`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.Height`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.OrdinarySuspension`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.geometricCarrier`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.join`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.joinSuspensionHomeomorph`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.mem_geometricCarrier_iff`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.support`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionCoordinates`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionMap`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionMap_fibres`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionQuotientMap`
- Truth anchor: `D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension.suspensionSetoid`
