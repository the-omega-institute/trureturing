# Round quaternion reconstruction on four vertices

## Abstract

Every round unit-quaternion gain assignment on four vertices admits a fit at four fifths of its triangle defect.

The vertices are the four elements of Fin(4). The unit quaternions form the round three-sphere, with distance given by the arccosine of the real inner product. Write Q for the assignment with identity spokes, gains I on the directed rim 12, 23, 31 and inverse gains on the reversed edges, where I is the quaternion with imaginary coordinates (1,0,0).

Write D(g,e) for inverse reversal, identity diagonal and a distance of at most e between the ordered product along two triangle sides and the gain along the third. Write F(g,p,r) when the directed edge distances between g and the gain induced by p are all at most r.

**Theorem 1.1 (Uniform reconstruction).**

$$\forall g \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to S^{3}\right),\; \forall e \in \mathbb{R},\; (0 \leq e) \Rightarrow ((e \leq \pi) \Rightarrow ((\operatorname{D}\left(g, e\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(4\right) \to S^{3},\; \operatorname{F}\left(g, p, \frac{4}{5} \cdot e\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.reconstruction_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For large defects, choose successive potentials orthogonal to each already assigned potential transported along its edge. For smaller defects, gauge the spokes to one. The middle two potentials are constrained by two pairs of spherical centers. Compare their normalized sums and move toward the opposite midpoint when their separation permits. At larger separations, project a common direction orthogonally to the center planes. Six rational interval estimates for cosine guarantee the four center inequalities and the remaining edge inequality.

**Theorem 1.2 (The cyclic quarter-turn optimum).**

$$(\operatorname{D}\left(Q, \frac{\pi}{2}\right)) \land ((\exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; (i \neq j) \land ((j \neq k) \land ((i \neq k) \land (\operatorname{d}\left(Q\left(i, j\right) \cdot Q\left(j, k\right), Q\left(i, k\right)\right) = \frac{\pi}{2})))) \land ((\forall p \in \operatorname{Fin}\left(4\right) \to S^{3},\; \exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; (i \neq j) \land (\operatorname{arccos}\left(\frac{1}{\sqrt{3}}\right) \leq \operatorname{d}\left(Q\left(i, j\right), \operatorname{inv}\left(\operatorname{p}\left(i\right)\right) \cdot \operatorname{p}\left(j\right)\right))) \land ((\exists p \in \operatorname{Fin}\left(4\right) \to S^{3},\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; (i \neq j) \Rightarrow (\operatorname{d}\left(Q\left(i, j\right), \operatorname{inv}\left(\operatorname{p}\left(i\right)\right) \cdot \operatorname{p}\left(j\right)\right) = \operatorname{arccos}\left(\frac{1}{\sqrt{3}}\right))) \land (\frac{3}{5} < \frac{2 \cdot \operatorname{arccos}\left(\frac{1}{\sqrt{3}}\right)}{\pi}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.quarter_turn_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three spoke projections bound the squared length of the rim mean from below by the square of the smallest edge cosine. The sum of the skew products on the rim equals the skew product of two orthogonal coordinates of the centered rim vectors multiplied by the square root of three. The Cauchy–Schwarz inequality and the centered energy identity bound the three skew products jointly. An equilateral configuration in the imaginary plane perpendicular to I attains equality on all edges.

**Theorem 1.3 (Obstruction to a smaller coefficient).**

$$\neg (\exists k \in \mathbb{R},\; (k < \frac{2 \cdot \operatorname{arccos}\left(\frac{1}{\sqrt{3}}\right)}{\pi}) \land (\forall g \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to S^{3}\right),\; \forall e \in \mathbb{R},\; (0 \leq e) \Rightarrow ((e \leq \pi) \Rightarrow ((\operatorname{D}\left(g, e\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(4\right) \to S^{3},\; \operatorname{F}\left(g, p, k \cdot e\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.not_subcritical_claim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate the proposed coefficient on the cyclic quarter-turn assignment at defect pi over two. Its exact minimax radius gives the contradiction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.not_subcritical_claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.quarter_turn_sharp`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.reconstruction_bound`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](../../../Quantum/AURICOmega/QuaternionComparisonModel.md)
