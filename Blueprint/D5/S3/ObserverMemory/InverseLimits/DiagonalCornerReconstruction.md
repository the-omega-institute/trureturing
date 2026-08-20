# Diagonal Corner Reconstruction

## Abstract

Coordinate corners recover every transition of a transfer operator.

**Theorem 1.1 (Diagonal corner reconstruction formula).**

$$\begin{gathered}\forall Y, \forall \tau: Y \to Y, \forall y, z \in Y,\\(P_{z}L_{\tau}P_{y} \neq 0 \iff z = \tau(y)) \land\\(z = \tau(y) \Rightarrow P_{z}L_{\tau}P_{y}e_{y} = e_{z}) \land\\(z \neq \tau(y) \Rightarrow P_{z}L_{\tau}P_{y} = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/DiagonalCornerReconstruction.diagonal_corner_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary state type Y and map tau, the basis vector at y is the finitely supported unit coordinate. The coordinate projection is evaluation at y followed by injection into that coordinate.

The imported transfer operator is constructed from the source map by Finsupp.lmapDomain. Its action on a unit coordinate is exactly the unit coordinate at the image state.

Composing the source-coordinate projection, transfer, and target-coordinate projection leaves the image basis vector when z is tau(y). The exact coordinate evaluation lemmas make the composition zero otherwise, which also proves the nonzero criterion.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/DiagonalCornerReconstruction.diagonal_corner_reconstruction`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics](TraceRankCombinatorics.md)
