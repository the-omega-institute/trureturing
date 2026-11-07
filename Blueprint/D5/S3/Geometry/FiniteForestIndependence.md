# Native independence realizations of finite forests

## Abstract

The actual independence realization of a finite forest is empty, contractible, or a sphere up to homotopy.

Let V be any finite type, in any universe, with decidable equality, and let G be a simple graph on V. Ispace(G) is the actual barycentric coordinate realization of its nonempty independent faces. There is no connectedness assumption. StdSphere(n) is the unit sphere in real Euclidean space with n+1 coordinates; StdSphere(0) consists of two points.

**Definition 1.1 (The residual labels).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.residualSet`

*Formalization.* `D5/S3/Geometry/FiniteForestIndependence.residualSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite decidable V, simple graph G and v in V, residualSet(G,v) is the set of x with no edge from v to x and x distinct from v. Its induced graph therefore retains precisely the labels outside the closed neighborhood of v.

**Definition 1.2 (Deleted neighbors).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.deleted`

*Formalization.* `D5/S3/Geometry/FiniteForestIndependence.deleted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every G and u,v in V, deleted(G,u,v) is the finite set of d adjacent to v and distinct from u. The vertex u never belongs to it.

**Definition 1.3 (The retained-label bijection).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.leafLabelsEquiv`

*Formalization.* `D5/S3/Geometry/FiniteForestIndependence.leafLabelsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every G,u,v with an edge u-v, the actual subtype of labels outside deleted(G,u,v) is equivalent to residualSet(G,v) disjoint-sum Bool. The forward map sends u to right true, v to right false, and every other retained vertex to its own residual label. The inverse returns that original residual label, u, or v respectively. Both inverse laws hold. No leaf hypothesis is needed for this bijection.

**Definition 1.4 (The actual retained graph splits).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.leafGraphIso`

*Formalization.* `D5/S3/Geometry/FiniteForestIndependence.leafGraphIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every G,u,v with an edge u-v and with every neighbor of u equal to v, the disjoint graph consisting of G induced on residualSet(G,v) and the complete graph on Bool is isomorphic to G induced outside deleted(G,u,v). The isomorphism is the inverse retained-label bijection. Residual adjacency is unchanged, the two right labels form exactly one edge, and all cross adjacencies are absent: residual vertices are not adjacent to v, and the unique-neighbor condition rules out adjacency to u.

**Definition 1.5 (Native leaf reduction to the augmented join).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.leafEquiv`

*Formalization.* `D5/S3/Geometry/FiniteForestIndependence.leafEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite decidable V,G,u,v under the edge and unique-neighbor hypotheses above, Ispace(G) is homotopy equivalent to the actual realization of the simplicial join of the residual independence complex with twoPoints. The maps compose simultaneous open-neighborhood folding with the actual graph-isomorphism coordinate homeomorphism and the disjoint-sum complex identity. The result includes an empty residual and an empty deleted set. It does not assume a homotopy model for G.

**Theorem 1.6 (Contraction from an isolated vertex).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.isolated_contractible`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteForestIndependence.isolated_contractible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable V, graph G and vertex u with no neighbor, Ispace(G) is contractible. Every independent face remains independent after adjoining u. The native cone segment contracts the entire actual realization to its coordinate vertex at u, including singleton graphs.

**Theorem 1.7 (Classification of every finite forest).**

Lean statement: `D5/S3/Geometry/FiniteForestIndependence.classification`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteForestIndependence.classification` (`✓ std3`). ∎

*Citation.* Richard Ehrenborg and Gábor Hetyei (2006). *The topology of the independence complex*. DOI: [10.1016/j.ejc.2005.04.010](https://doi.org/10.1016/j.ejc.2005.04.010).

*Commentary.*

For every V in any universe with Fintype and DecidableEq, and every simple graph G on V, G.IsAcyclic implies: V is empty, or Ispace(G) is contractible, or there exists a natural number n and a homotopy equivalence from Ispace(G) to StdSphere(n). A nonempty forest has a vertex with at most one neighbor. An isolated vertex gives the cone contraction. Otherwise the native leaf equivalence applies. The induced residual is acyclic and has strictly fewer vertices because v is excluded. Cardinal induction classifies this residual. If it is empty, the augmented empty-left join unit and the two-point homeomorphism give exactly S0. For a nonempty residual, the actual realization-to-ordinary-join homeomorphism applies. A contractible factor contracts the join; a sphere of dimension d gives dimension d+1 by joining with S0. Disconnected forests and zero-dimensional sphere outcomes are included.

This is the classical forest classification of Ehrenborg and Hetyei, The topology of the independence complex, European Journal of Combinatorics 27 (2006), 906-923, Corollary 6.1. The construction here uses the actual finite-coordinate spaces and maps. It does not identify the sphere dimension for every path or assert a modulo-three path recurrence.

## References

- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.classification`
- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.deleted`
- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.isolated_contractible`
- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.leafEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.leafGraphIso`
- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.leafLabelsEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteForestIndependence.residualSet`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError](../Combinatorics/SpectralGraph/ScalarCycleRowError.md)
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/Transport](FiniteComponentClosure/Transport.md)
- Dependency: [D5/S3/Geometry/FiniteGraphIndependenceReduction](FiniteGraphIndependenceReduction.md)
