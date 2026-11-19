# Gray reconstruction through the nineteen-point threshold

## Abstract

Every nonempty actual Huang-balanced induced cubic Q9 support with a coordinate-zero slice of size at most nineteen is a total cube-symmetry image of Gray support3.

Q9 is Fin 9 to Bool, flip is BalancedCriticalSpectrum.flip, and C is the original finite support with its actual induced cube graph and the fixed Huang signing. coordinateSlice C b is the coordinate-zero filter. GraySupport(d) means GrayGridComponent.support d. The two equivalences in the conclusion act on the entire cube and all nine coordinates. This conditional classification assumes no Gray normal form, supplied path certificate or connectedness.

**Theorem 1.1 (Reconstruction from an actual slice of at most nineteen vertices).**

$$\forall C \in \operatorname{Finset}\left(\operatorname{Q}\left(9\right)\right),\; (\operatorname{Nonempty}\left(C\right)) \Rightarrow ((\operatorname{IsRegularOfDegree}\left(\operatorname{induce}\left(\operatorname{hypercube}\left(9\right), C\right), 3\right)) \Rightarrow ((\operatorname{IsBalanced}\left(C\right)) \Rightarrow (\forall b \in \operatorname{Bool}\left(\right),\; (\operatorname{card}\left(\operatorname{coordinateSlice}\left(C, b\right)\right) \le 19) \Rightarrow (\exists g \in \operatorname{Equiv}\left(\operatorname{Q}\left(9\right), \operatorname{Q}\left(9\right)\right),\; \exists p \in \operatorname{Equiv}\left(\operatorname{Fin}\left(9\right), \operatorname{Fin}\left(9\right)\right),\; (\forall x \in \operatorname{Q}\left(9\right),\; \forall i \in \operatorname{Fin}\left(9\right),\; g\left(\operatorname{flip}\left(x, i\right)\right) = \operatorname{flip}\left(g\left(x\right), p\left(i\right)\right)) \land (C = \operatorname{image}\left(\operatorname{GraySupport}\left(3\right), g\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice.nineteen_point_slice_gray_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eighteen-point theorem handles every smaller slice. At nineteen vertices, the actual degree-two count is nine or eleven. Two depth-three trees about a high-high edge are disjoint by the girth-eight path argument. Each high first neighbor increases their lower bound by one. With eleven low vertices, there are only eight high vertices and at most two high vertices having a high neighbor. The roots account for those two; the tree layers then leave too few positions for all eight highs.

With nine low vertices, high-high incidences force a high vertex with two high neighbors. Equality in the nineteen-point tree count fixes all vertices. Its remaining incidences yield six cycle branch vertices, six cycle middles and three opposite matching middles, forming an induced once-subdivision of K3,3. A selected center has a two-edge cube path to each of the three matching middles.

Cubical subdivision rigidity gives an origin O and six distinct directions. The matching middles differ from O on three disjoint coordinate pairs P_i. If D is the differing-coordinate set between the selected center and O, each distance bound gives card(D) at most twice card(D intersect P_i). Summing gives three times card(D) at most twice card(D), so the center equals O. All six branch vertices are then selected neighbors of the center, contradicting its degree at most three. Only the two-edge paths are used; no degree assumption on their bridges is needed.

The result is a conditional reconstruction for the displayed actual slice bound. It does not establish the original external Q9 classification for arbitrary support or the full 258-point obstruction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice.nineteen_point_slice_gray_reconstruction`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceMatching](NineteenPointSliceMatching.md)
