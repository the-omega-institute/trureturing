# Sharp unit-quaternion reconstruction bounds

## Abstract

Triangle defects control reconstruction of unit-quaternion gains on finite chordal graphs.

Write SU(2) for the group of unit real quaternions. The round distance d is the arccosine of the real inner product. The vertex type may lie in any universe.

**Definition 1.1 (Skew gains).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; \operatorname{SU2Skew}\left(G, g\right) \Leftrightarrow (\forall u \in V,\; \forall v \in V,\; (\operatorname{Adj}\left(G, u, v\right)) \Rightarrow (\operatorname{g}\left(v, u\right) = \operatorname{g}\left(u, v\right)^{-1}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.SU2Skew` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversing an oriented edge inverts its gain.

**Definition 1.2 (Triangle defects).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; \forall delta \in \mathbb{R},\; \operatorname{SU2TriangleBound}\left(G, g, delta\right) \Leftrightarrow (\forall u \in V,\; \forall v \in V,\; \forall w \in V,\; (\operatorname{Adj}\left(G, u, v\right)) \Rightarrow ((\operatorname{Adj}\left(G, v, w\right)) \Rightarrow ((\operatorname{Adj}\left(G, u, w\right)) \Rightarrow (\operatorname{d}\left(\operatorname{g}\left(u, v\right) \operatorname{g}\left(v, w\right), \operatorname{g}\left(u, w\right)\right) \le delta))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.SU2TriangleBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The triangle defect compares the ordered two-edge product with the gain on the direct edge.

**Definition 1.3 (Potential residuals).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; \forall p \in V \to \operatorname{SU}\left(2\right),\; \forall r \in \mathbb{R},\; \operatorname{SU2Fits}\left(G, g, p, r\right) \Leftrightarrow (\forall u \in V,\; \forall v \in V,\; (\operatorname{Adj}\left(G, u, v\right)) \Rightarrow (\operatorname{d}\left(\operatorname{g}\left(u, v\right), \operatorname{p}\left(u\right)^{-1} \operatorname{p}\left(v\right)\right) \le r))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.SU2Fits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The potential assigns a unit quaternion to each vertex. The relative potential of an oriented edge is the inverse of the potential at its tail times the potential at its head.

**Theorem 1.4 (The global coefficient).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Finite}\left(V\right)] (\operatorname{IsChordal}\left(G\right)) \Rightarrow ((\operatorname{Connected}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; (\operatorname{SU2Skew}\left(G, g\right)) \Rightarrow (\forall delta \in \mathbb{R},\; (0 \le delta) \Rightarrow ((\operatorname{SU2TriangleBound}\left(G, g, delta\right)) \Rightarrow (\exists p \in V \to \operatorname{SU}\left(2\right),\; \operatorname{SU2Fits}\left(G, g, p, \frac{434}{125} delta\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_su2_gain_potential_global_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The breadth-first construction transports a frame along common shadow predecessors and normalizes the nearest point of each candidate hull. Across consecutive layers, two cap radii bound the residual. Within a layer, nested predecessor sets give corresponding candidates in the two caps. In the lower defect interval, a projection of their convex mean gives the comparison. In the upper interval, three Rayleigh quotients for the same weighted holonomy matrix force a common quaternionic eigenline with large overlap. The asymmetric overlap inequality and the rational interval estimates exclude the resulting angle. When the proposed bound reaches pi, the diameter of the unit three-sphere suffices.

**Theorem 1.5 (Defects at most pi over six).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Finite}\left(V\right)] (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; (\operatorname{SU2Skew}\left(G, g\right)) \Rightarrow (\forall delta \in \mathbb{R},\; (0 \le delta) \Rightarrow ((delta \le \frac{\pi}{6}) \Rightarrow ((\operatorname{SU2TriangleBound}\left(G, g, delta\right)) \Rightarrow (\exists p \in V \to \operatorname{SU}\left(2\right),\; \operatorname{SU2Fits}\left(G, g, p, 2 delta\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_su2_gain_potential_small_defect_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse simplicial elimination inserts a cap center at each vertex. The residual on the parent clique and the triangle defect give a candidate diameter at most three times the defect. The four-point spherical Jung criterion follows from the triple-angle and double-angle identities.

**Theorem 1.6 (Defects at most one tenth).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Finite}\left(V\right)] (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; (\operatorname{SU2Skew}\left(G, g\right)) \Rightarrow (\forall delta \in \mathbb{R},\; (0 \le delta) \Rightarrow ((delta \le \frac{1}{10}) \Rightarrow ((\operatorname{SU2TriangleBound}\left(G, g, delta\right)) \Rightarrow (\exists p \in V \to \operatorname{SU}\left(2\right),\; \operatorname{SU2Fits}\left(G, g, p, \frac{8}{5} delta\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_su2_gain_potential_small_defect_eight_fifths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same simplicial insertion uses the spherical Jung cosine criterion with radius eight fifths of the defect. Cubic and linear sine bounds certify the criterion on the entire interval.

**Theorem 1.7 (At most two parents).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Finite}\left(V\right)] (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; (\operatorname{SU2Skew}\left(G, g\right)) \Rightarrow (\forall delta \in \mathbb{R},\; (0 \le delta) \Rightarrow ((\operatorname{SU2TriangleBound}\left(G, g, delta\right)) \Rightarrow ((\forall S \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{coe}\left(S\right)\right)) \Rightarrow (\operatorname{card}\left(S\right) \le 3)) \Rightarrow (\exists p \in V \to \operatorname{SU}\left(2\right),\; \operatorname{SU2Fits}\left(G, g, p, \operatorname{min}\left(delta, \frac{\pi}{2}\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_cliqueThree_su2_gain_potential_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at most two parents, half the candidate diameter bounds the insertion radius for defects below pi over two. The closed-hemisphere estimate gives the radius pi over two for larger defects.

**Theorem 1.8 (At most three parents).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Finite}\left(V\right)] (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; (\operatorname{SU2Skew}\left(G, g\right)) \Rightarrow (\forall delta \in \mathbb{R},\; (0 \le delta) \Rightarrow ((\operatorname{SU2TriangleBound}\left(G, g, delta\right)) \Rightarrow ((\forall S \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{coe}\left(S\right)\right)) \Rightarrow (\operatorname{card}\left(S\right) \le 4)) \Rightarrow (\exists p \in V \to \operatorname{SU}\left(2\right),\; \operatorname{SU2Fits}\left(G, g, p, 2 delta\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_cliqueFour_su2_gain_potential_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three-point Jung cap handles defects through pi over five. Between pi over five and pi over four, the initial two spectral moments and the cubic triangle holonomy moment exclude a nearest point with norm below the target cosine. From pi over four onward the closed-hemisphere radius suffices.

**Theorem 1.9 (At most four parents).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Finite}\left(V\right)] (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall g \in V \to \left(V \to \operatorname{SU}\left(2\right)\right),\; (\operatorname{SU2Skew}\left(G, g\right)) \Rightarrow ((\forall S \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{coe}\left(S\right)\right)) \Rightarrow (\operatorname{card}\left(S\right) \le 5)) \Rightarrow (\exists p \in V \to \operatorname{SU}\left(2\right),\; \operatorname{SU2Fits}\left(G, g, p, \frac{\pi}{2}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_cliqueFive_su2_gain_potential_half_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine span of at most four unit quaternions has dimension at most three. A unit normal with the appropriate sign gives a closed hemisphere containing every insertion candidate.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.SU2Fits`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.SU2Skew`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.SU2TriangleBound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_cliqueFive_su2_gain_potential_half_pi`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_cliqueFour_su2_gain_potential_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_cliqueThree_su2_gain_potential_min`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_su2_gain_potential_global_sharp`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_su2_gain_potential_small_defect_eight_fifths`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds.exists_su2_gain_potential_small_defect_two`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential](../UniformGainPotential.md)
