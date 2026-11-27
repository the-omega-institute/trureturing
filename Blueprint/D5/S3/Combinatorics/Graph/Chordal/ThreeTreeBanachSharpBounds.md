# Banach reconstruction on clique-four chordal graphs

## Abstract

A polygon invariant bounds Banach gain reconstruction on clique-four chordal graphs. Third powers of paths have supremum reconstruction coefficient four thirds.

Let skew(V,g) mean that reversing a gain negates it for every ordered pair of vertices in V. Let flat(G,g,e) mean that the norm of g(i,j) plus g(j,k) minus g(i,k) is at most e on every ordered triangle of G. Write err(g,p,i,j) for the norm of g(i,j) minus the entire difference (p(j) minus p(i)). The predicate fit(G,g,p,e) requires this norm to be at most e on every ordered edge.

**Theorem 1.1 (Reconstruction from the invariant polygon).**

$$\forall u \in \operatorname{Universe},\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow ((\forall A \in \operatorname{Set}\left(V\right),\; (\operatorname{IsClique}\left(G, A\right)) \Rightarrow (\operatorname{ncard}\left(A\right) \le 4)) \Rightarrow (\forall v \in \operatorname{Universe},\; \forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall g \in V \to \left(V \to E\right),\; \forall e \in \mathbb{R},\; (0 \le e) \Rightarrow ((\operatorname{skew}\left(V, g\right)) \Rightarrow ((\operatorname{flat}\left(G, g, e\right)) \Rightarrow (\exists p \in V \to E,\; \operatorname{fit}\left(G, g, p, (\frac{72537}{50000}) \cdot e\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.exists_cliqueFour_banach_gain_potential_polygon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use a reverse perfect elimination order. For an ordered parent triangle record the two consecutive residuals and its defect. The middle residual into the next vertex is a fixed linear expression in those two residuals and three defects. Each of the nine signed transitions preserves the thirteen polygon inequalities by nonnegative combinations of pairs of parent inequalities. Six signed possibilities cover every admissible scalar defect quadruple by convex combinations.

A single predecessor fixes the new potential by exact transport. For two predecessors append a virtual copy of the later predecessor. Its potential puts the parent in the zero-defect layer, and midpoint interpolation gives opposite half-defects on the two virtual child faces. The child face of the three actual vertices therefore carries the invariant into later attachments. Apply the scalar argument to each norm-one-or-smaller functional and use a norming functional to recover the edge norm. An arbitrarily small positive allowance handles zero defect tolerance.

**Definition 1.2 (The path graph).**

$$\forall n \in \mathbb{N},\; \operatorname{P}\left(n\right) = \operatorname{pathPower}\left(n, 3\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph joins distinct indices at distance at most three.

**Definition 1.3 (The causal potential on a path).**

$$\forall n \in \mathbb{N},\; \forall v \in \operatorname{Universe},\; \forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall g \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to E\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{causal}\left(n, g, i\right) = \operatorname{I}\left(g, \operatorname{val}\left(i\right)+2\right)+\operatorname{J}\left(g, \operatorname{val}\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_causal_potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend the vertex indices by repeating the endpoints, with the original vertex zero at index two. Write I for the integral of the adjacent gains in this indexing, starting at zero. Write val(i) for the natural index of a vertex i. Subtract the gradient of I and denote the remaining gains of lengths two and three by a and b. Write J(g,k) for the sum over natural indices j less than k of (b(j) minus a(j) plus a(j+1)) divided by three term by term.

**Theorem 1.4 (Error of the causal path potential).**

$$\forall n \in \mathbb{N},\; \forall v \in \operatorname{Universe},\; \forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall g \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to E\right),\; \forall e \in \mathbb{R},\; (0 \le e) \Rightarrow ((\operatorname{skew}\left(\operatorname{Fin}\left(n\right), g\right)) \Rightarrow ((\operatorname{flat}\left(\operatorname{P}\left(n\right), g, e\right)) \Rightarrow (\operatorname{fit}\left(\operatorname{P}\left(n\right), g, \operatorname{causal}\left(n, g\right), (\frac{4}{3}) \cdot e\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_causal_potential_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrate along the adjacent edges, then subtract that gradient. Call the remaining gains on lengths two and three a and b. Clamp the indices at the endpoints, and index the increments by the ordinary vertex indices. The increment from i to i+1 is one third of the sum of b at i minus two, minus a at i minus two, plus a at i minus one. The residuals on lengths one, two, and three sum two, three, and four terms respectively, each bounded by the triangle tolerance, and divide by three.

**Theorem 1.5 (Existence of a path potential).**

$$\forall n \in \mathbb{N},\; \forall v \in \operatorname{Universe},\; \forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall g \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to E\right),\; \forall e \in \mathbb{R},\; (0 \le e) \Rightarrow ((\operatorname{skew}\left(\operatorname{Fin}\left(n\right), g\right)) \Rightarrow ((\operatorname{flat}\left(\operatorname{P}\left(n\right), g, e\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(n\right) \to E,\; \operatorname{fit}\left(\operatorname{P}\left(n\right), g, p, (\frac{4}{3}) \cdot e\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_banach_upper_four_thirds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the causal potential from the preceding theorem.

**Definition 1.6 (The hexagonal plane).**

$$\forall x \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; x \in Hex \Leftrightarrow \operatorname{x}\left(0\right)+\operatorname{x}\left(1\right)+\operatorname{x}\left(2\right) = 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathHexagon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The norm is the restriction of the supremum norm on the three coordinates.

**Theorem 1.7 (A finite planar lower bound).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\exists g \in \operatorname{Fin}\left(3 \cdot m+3\right) \to \left(\operatorname{Fin}\left(3 \cdot m+3\right) \to Hex\right),\; (\operatorname{skew}\left(\operatorname{Fin}\left(3 \cdot m+3\right), g\right)) \land ((\operatorname{flat}\left(\operatorname{P}\left(3 \cdot m+3\right), g, 1\right)) \land (\forall p \in \operatorname{Fin}\left(3 \cdot m+3\right) \to Hex,\; \exists i \in \operatorname{Fin}\left(3 \cdot m+3\right),\; \exists j \in \operatorname{Fin}\left(3 \cdot m+3\right),\; (\operatorname{Adj}\left(\operatorname{P}\left(3 \cdot m+3\right), i, j\right)) \land (\frac{4 \cdot \operatorname{real}\left(m\right)}{3 \cdot \operatorname{real}\left(m\right)+4} \le \operatorname{err}\left(g, p, i, j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_banach_lower_four_thirds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The length-three gain is two thirds in every coordinate except the initial index modulo three, where it is minus four thirds. A length-two gain averages the current and previous length-three gains. Adjacent gains vanish. Sum the residuals along each of the three length-three residue classes, taking its corresponding coordinate. The zero coordinate sums at the two middle endpoints leave four adjacent-edge differences. If M bounds the residuals, the resulting inequality is four times m at most three times m plus four, multiplied by M.

**Theorem 1.8 (Supremum over path lengths).**

$$\operatorname{sup}\left((n:\mathbb{N} \mapsto \operatorname{CBan}\left(n, 3\right))\right) = \frac{4}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_banach_sup_four_thirds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here CBan is the infimum of nonnegative uniform reconstruction coefficients at unit defect for the indicated path power. The causal formula supplies a common upper bound. The path-coefficient convergence theorem at width three gives the matching lower bound on the supremum.

**Definition 1.9 (The clique-four coefficient).**

$$S = \operatorname{inf}\left(\operatorname{Good}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.cliqueFourBanachCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Good is the set of nonnegative real coefficients giving a uniform potential bound at unit triangle defect for every finite chordal graph of clique number at most four and every real Banach target. S is the infimum of Good.

**Theorem 1.10 (The clique-four interval).**

$$(\frac{4}{3} \le S) \land ((S \le \frac{72537}{50000}) \land (\frac{72537}{50000} < \frac{3}{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.cliqueFour_banach_coefficient_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible coefficient bounds the reconstruction coefficients of every third power of a path. These graphs are chordal and have no clique of size five, so the path supremum gives the lower endpoint. The polygon coefficient is itself admissible.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.cliqueFourBanachCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.cliqueFour_banach_coefficient_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.exists_cliqueFour_banach_gain_potential_polygon`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathHexagon`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_banach_lower_four_thirds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_banach_sup_four_thirds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_banach_upper_four_thirds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_causal_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.pathPowerThree_causal_potential_error`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/EliminationForest](EliminationForest.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential](SimplicialAndIntervalPotential.md)
