# A signed residual at two flips from a connector

## Abstract

A signed residual at two flips from a connector

**Theorem 1.1 (A third actual neighbour forces a two-flip discrepancy).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ConnectorResidual.residual_at_connector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ConnectorResidual.residual_at_connector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a coherently switched cubic support and an actual odd singleton x in axial layer b with two adjacent even dimer fibres. The integer dimer word d is nonzero exactly on the even paired fibres. The prescribed contact word c satisfies Hc = 4d on even sites and agrees with the parity-gauged sum g at x, where H is the signed transverse operator.

Cubic degree gives three selected neighbour directions at the actual vertex over x. Each dimer supplies one transverse direction in layer b. The axial mate of x is absent, so the remaining direction i leads to an actual neighbour in the same layer. Its projection y is even and has d(y) = 0. The dimer support condition rules out an axial mate at y, making it a singleton.

At y the sum g has value ±1. Its folded equation gives Hg(y) = 2g(y) ≠ 0, whereas the prescribed row is Hc(y) = 4d(y) = 0. The signed rows differ, so some transverse flip j of y reaches a site where g and c differ. Flipping i back would return to x, where they agree. Thus j differs from i and the discrepancy is at an odd site two flips from x.

In the intended application to the normalized order-ninety cylinder for Hong–Wu–Xia, arXiv:2610.09483 §7, Problem 2, take d to be the signed majority-dimer word and c the signed contact word. The conclusion puts an odd site in the support of g − c. When the chart also gives agreement on all prescribed contacts and c vanishes elsewhere, the site is an actual odd singleton outside the contacts, since the sum vanishes at empty fibres and odd paired fibres. The local result applies when the cylinder chart supplies the dimer support, the even contact row and agreement at the chosen connector.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ConnectorResidual.residual_at_connector`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold](Q9SignedAxialFold.md)
