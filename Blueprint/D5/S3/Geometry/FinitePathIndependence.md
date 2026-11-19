# Native independence realizations of paths

## Abstract

The exact modulo-three homotopy types of the native independence realizations of paths.

For each natural number n, let X(n) be FiniteCoordinateTruncation.Ispace of SimpleGraph.pathGraph(n), on the original labels Fin(n). Thus X(n) consists of nonnegative real coordinate vectors with total sum one, such that each consecutive pair has a zero coordinate. These are the actual realizations of nonempty independent faces. StdSphere(k) is the unit sphere in real Euclidean space with k+1 coordinates.

**Theorem 1.1 (Complete path classification).**

Lean statement: `D5/S3/Geometry/FinitePathIndependence.classification`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePathIndependence.classification` (`✓ std3`). ∎

*Citation.* Richard Ehrenborg and Gábor Hetyei (2006). *The topology of the independence complex*. DOI: [10.1016/j.ejc.2005.04.010](https://doi.org/10.1016/j.ejc.2005.04.010).

*Commentary.*

X(0) is empty. For every natural number k, there exists a homotopy equivalence X(3*(k+1)) to StdSphere(k); X(3*k+1) is contractible; and there exists a homotopy equivalence X(3*k+2) to StdSphere(k). All three quantifiers include k=0. In particular X(1) is contractible and both X(2) and X(3) have the homotopy type of the zero-sphere.

In the path with n+3 vertices, a vertex i of Fin(n+3) has original printed label i.val+1. Choose the last leaf, with Fin value n+2 and printed label n+3, and its neighbor, with Fin value n+1 and printed label n+2. In the one-based theory notation, the last three printed labels are v=n+1, u=n+2, w=n+3, so the last leaf is w. Adjacency means that the two Fin values (equivalently, their printed labels) differ by one. A vertex i lies outside the closed neighborhood of that neighbor exactly when i.val<n. Sending i to the element of Fin(n) with the same Fin value gives a bijection preserving the original printed label i.val+1, with inverse the inclusion at the same value. The adjacency formula proves that this is an isomorphism of the induced residual graph with the path on n vertices.

The native leaf equivalence identifies X(n+3) up to homotopy with the realization of the residual independence complex joined simplicially to the two-point complex. The residual graph isomorphism extends by the identity on the disjoint Bool edge. Its coordinate homeomorphism and the disjoint-graph complex identities transport the whole augmented join, including n=0.

The empty path has no probability vector because its coordinate sum is zero. The one-vertex path contracts to its isolated vertex. For the two-vertex path, leaf reduction has empty residual. For the three-vertex path, the reduction with n=0 also has empty residual. The empty-left simplicial join homeomorphism, taken in its inverse direction, identifies each reduced realization with the two-point space, which is homeomorphic to StdSphere(0). The ordinary join with an empty factor is not used in these cases.

For a nonempty residual realization, the barycentric join homeomorphism permits ordinary joins. An equivalence to StdSphere(k) supplies a point by pulling back its coordinate point; joining with StdSphere(0) then gives StdSphere(k+1). In the contractible case, transport first to Unit, whose ordinary join contracts by the point-join contraction. Simultaneous induction from X(3), X(1), and X(2), adding three vertices each time, proves the three exact families with the stated dimensions.

Ehrenborg and Hetyei, The topology of the independence complex, European Journal of Combinatorics 27 (2006), Proposition 6.2(ii), page 916, gives the three-vertex suspension mechanism; Corollary 6.3, page 917, gives the path classification indexed by vertex count and reduces it to n=1,2,3. The n=0 clause here records the separate empty native realization convention.

## References

- Truth anchor: `D5/S3/Geometry/FinitePathIndependence.classification`
- Dependency: [D5/S3/Geometry/FiniteForestIndependence](FiniteForestIndependence.md)
