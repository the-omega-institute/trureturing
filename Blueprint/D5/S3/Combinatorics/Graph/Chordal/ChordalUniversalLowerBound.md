# Sharp gain reconstruction on path powers

## Abstract

Path powers admit uniform reconstruction with coefficient two. The width-three path on twelve vertices gives a sharp integral obstruction.

The graph P(n,k) has vertex set Fin(n). Two distinct indices are adjacent when their difference has absolute value at most k.

**Theorem 1.1 (Chordality of path powers).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{Chordal}\left(\operatorname{P}\left(n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_isChordal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eliminate vertices in increasing order. The remaining neighbours of a vertex lie in the next k positions and hence form a clique.

For multiplicative gains, R(G,g) means that the reversed gain is the inverse on each edge. T(G,g,e) means that on each ordered triangle the distance between the product along the first two sides and the gain along the third side is at most e. F(G,g,p,r) means that each directed edge gain is within distance r of the inverse of the potential at its tail times the potential at its head. The versions Radd, Tadd, and Fadd use negation, addition, and the head potential minus the tail potential. The functions edgeError(g,p,i,j) and edgeErrorAdd(g,p,i,j) are the respective multiplicative and additive distances at the single directed edge from i to j.

**Theorem 1.2 (Uniform coefficient two).**

$$\forall H \in \mathrm{Type},\; [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(H^{op}, H\right)] \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (1 \leq k) \Rightarrow (\forall g \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to H\right),\; \forall e \in \mathbb{R},\; (0 \leq e) \Rightarrow ((\operatorname{R}\left(\operatorname{P}\left(n, k\right), g\right)) \Rightarrow ((\operatorname{T}\left(\operatorname{P}\left(n, k\right), g, e\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(n\right) \to H,\; \operatorname{F}\left(\operatorname{P}\left(n, k\right), g, p, 2 \cdot e\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_exists_two_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Join all vertices to their block heads and join successive heads. The tree potential compares each same-block edge with one triangle through its head. On a cross-block edge the earlier endpoint is adjacent to the later head, giving two triangle comparisons.

Write X for the real cycle coordinates and L for their integral multiplicative counterpart. Both use the 19 coordinates outside the lexicographic greedy spanning tree. The filling norm is the infimum of the sum of absolute face coefficients over the 28 oriented triangles with the given boundary. The integer infimum is a minimum. The real filling norm makes X a finite-dimensional Banach space. Write gR for the canonical real gains, and gZ(n) for the integral gains pulled back along the map that sends vertices beyond 11 to 11.

**Theorem 1.3 (Real and integral lower bounds on twelve vertices).**

$$(\operatorname{Radd}\left(\operatorname{P}\left(12, 3\right), gR\right)) \land ((\operatorname{Tadd}\left(\operatorname{P}\left(12, 3\right), gR, 1\right)) \land ((\forall p \in \operatorname{Fin}\left(12\right) \to X,\; \exists i \in \operatorname{Fin}\left(12\right),\; \exists j \in \operatorname{Fin}\left(12\right),\; (\operatorname{Adj}\left(\operatorname{P}\left(12, 3\right), i, j\right)) \land (\frac{49}{48} \leq \operatorname{edgeErrorAdd}\left(gR, p, i, j\right))) \land ((\operatorname{R}\left(\operatorname{P}\left(12, 3\right), \operatorname{gZ}\left(12\right)\right)) \land ((\operatorname{T}\left(\operatorname{P}\left(12, 3\right), \operatorname{gZ}\left(12\right), 1\right)) \land (\forall p \in \operatorname{Fin}\left(12\right) \to L,\; \exists i \in \operatorname{Fin}\left(12\right),\; \exists j \in \operatorname{Fin}\left(12\right),\; (\operatorname{Adj}\left(\operatorname{P}\left(12, 3\right), i, j\right)) \land (2 \leq \operatorname{edgeError}\left(\operatorname{gZ}\left(12\right), p, i, j\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_three_banach_and_integral_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual equality weights annihilate potential differences, because the boundary of each triangle has zero incidence at the vertices. The weighted residual functional is 98, and the column bounds give coefficients of total mass 96. The real maximum is therefore at least 49/48. Each integral filling is also a real filling, and its integral length raises the lower bound to two.

**Theorem 1.4 (Exact coefficient in width three).**

$$\forall n \in \mathbb{N},\; (12 \leq n) \Rightarrow ((\operatorname{R}\left(\operatorname{P}\left(n, 3\right), \operatorname{gZ}\left(n\right)\right)) \land ((\operatorname{T}\left(\operatorname{P}\left(n, 3\right), \operatorname{gZ}\left(n\right), 1\right)) \land ((\forall p \in \operatorname{Fin}\left(n\right) \to L,\; \exists i \in \operatorname{Fin}\left(n\right),\; \exists j \in \operatorname{Fin}\left(n\right),\; (\operatorname{Adj}\left(\operatorname{P}\left(n, 3\right), i, j\right)) \land (2 \leq \operatorname{edgeError}\left(\operatorname{gZ}\left(n\right), p, i, j\right))) \land (\exists p \in \operatorname{Fin}\left(n\right) \to L,\; \operatorname{F}\left(\operatorname{P}\left(n, 3\right), \operatorname{gZ}\left(n\right), p, 2\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_three_exact_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cloning the final vertex preserves the triangle condition. Each new triangle maps to an old triangle, a backtrack, or the diagonal. Restriction to the first twelve vertices preserves the obstruction. The block-head potential supplies the matching upper bound.

**Theorem 1.5 (Obstruction to a sub-two chordal coefficient).**

$$\neg(\exists C \in \mathbb{R},\; (C < 2) \land (\forall V \in \mathrm{Type},\; [\operatorname{Finite}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{Chordal}\left(G\right)) \Rightarrow (\forall H \in \mathrm{Type},\; [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(H^{op}, H\right)] \forall g \in V \to \left(V \to H\right),\; \forall e \in \mathbb{R},\; (0 \leq e) \Rightarrow ((\operatorname{R}\left(G, g\right)) \Rightarrow ((\operatorname{T}\left(G, g, e\right)) \Rightarrow (\exists p \in V \to H,\; \operatorname{F}\left(G, g, p, C \cdot e\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.not_subtwo_universal_chordal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the width-three graph on twelve vertices and its integral gains at triangle defect one. Every potential has an edge with error at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.not_subtwo_universal_chordal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_exists_two_approximate_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_isChordal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_three_banach_and_integral_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_three_exact_two`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Characterization](Characterization.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/UniformGainPotential](UniformGainPotential.md)
