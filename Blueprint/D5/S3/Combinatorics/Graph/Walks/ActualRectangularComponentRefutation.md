# Componentwise balance fails for actual rectangular residuals

## Abstract

An actual feasible rectangle can have a residual connected component with more original edges than total capacity.

**Definition 1.1 (The universal componentwise assertion).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive natural a,b, take a finite edge identity type E, two maps src,dst from E to Fin(2a) times Fin(2b), and a finite vertex set T. Each original edge must join square-grid neighbors. The endpoint map on E times Bool is injective, and both endpoints of every edge lie outside T. Write A for T together with all endpoints. Each vertex in T has at most one square-grid neighbor in A.

Use the tile map kappa(x)=(floor(x.row/2),floor(x.column/2)). Let t(Q) count vertices of T in Q, h(Q) count original matching identities internal to Q, and s(Q) count original matching identities joining Q to a distinct tile containing two vertices of T. Set r(Q)=2-(t(Q)+h(Q)+s(Q)), using natural subtraction. These are the same quantities as in `D5/S3/Combinatorics/Graph/ActualRectangularResidualBridge.actual_even_rectangular_residual_bridge`.

Retain precisely the original edge identities with distinct endpoint tiles and with t less than two at both ends. Their source and destination tile maps are rs and rd. The graph is originalGraph(rs,rd), whose adjacency is supplied by `D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.originalGraph`. Its vertex set contains all a times b tiles, including saturated isolated tiles. Connectivity forgets parallel-edge multiplicity, while edge counts retain every original identity.

The assertion says that, for every connected component W of this graph, the number of residual identities whose source tile lies in W is at most the sum of r(Q) over all tiles Q in W. An edge has both ends in the same component, so the source convention counts each identity once.

**Theorem 1.2 (A feasible four by six counterexample).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal componentwise assertion is false. Number the vertices of the four by six rectangle by row, from zero to twenty-three. Take T={0,5,12,17,19,22} and the five distinct matching identities (1,2),(3,4),(7,13),(10,16),(8,9). The coordinate maps send a number k to (floor(k/6),k mod 6). Checking the actual square-grid adjacencies, the ten distinct endpoints, their disjointness from T, and the occupied neighbors of T establishes all feasibility hypotheses.

Apply the same tile map and residual rule to this realization. The component containing tile (0,0) consists exactly of (0,0),(0,1),(0,2), or tiles zero, one and two in row order. It contains the original identities (1,2) and (3,4), now joining consecutive tiles of that row. Their count is two. The capacities on these three tiles are zero, one and zero, so their sum is one. The universal assertion would require two to be at most one.

The component is taken in the original residual graph produced by the stated realization; its support is computed from connectivity. No additional geometric separation, planarity or routing hypothesis is imposed. The conclusion refutes componentwise balance alone. It does not assert a formula for all local port routings, a coefficient-one bound for all rectangles, or an odd-rectangle extension.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ActualRectangularResidualBridge.actual_even_rectangular_residual_bridge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRectangularComponentRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.originalGraph`
- Dependency: [D5/S3/Combinatorics/Graph/ActualRectangularResidualBridge](../ActualRectangularResidualBridge.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption](CapacityPortSeparationAbsorption.md)
