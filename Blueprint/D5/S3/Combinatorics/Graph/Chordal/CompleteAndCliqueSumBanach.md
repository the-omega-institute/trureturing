# Complete graph constants and separated clique sums

## Abstract

The complete graph has exact real Banach reconstruction coefficient (m minus two) over m. Separated clique sums admit a factor of two minus one over the maximum attachment size.

Write natcard for the natural-number cardinality and real for the natural-to-real cast. The norm is a seminorm for the upper estimates. Write skew(V,g) when every reversed gain is the negative of the original gain, including equal endpoints. Write triangle(V,g,e) when the norm of g(i,j)+g(j,l)-g(i,l) is at most e for every triple of pairwise distinct vertices. Write error(g,p,i,j) for the norm of g(i,j)-(p(j)-p(i)).

**Theorem 1.1 (Complete graph upper bound).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , (2 \le \operatorname{natcard}\left(V\right)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (\operatorname{skew}\left(V, g\right)) \Rightarrow ((\operatorname{triangle}\left(V, g, epsilon\right)) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (i \neq j) \Rightarrow (\operatorname{error}\left(g, phi, i, j\right) \le \frac{\operatorname{real}\left(\operatorname{natcard}\left(V\right)\right)-2}{\operatorname{real}\left(\operatorname{natcard}\left(V\right)\right)} \cdot epsilon))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.completeGraph_banach_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Average the star potentials with all possible centers. The residual on an ordered edge is the mean of the triangle expressions with each center. The two centers at the endpoints have zero residual. Each of the remaining centers contributes at most the triangle tolerance. The triangle inequality for the seminorm gives the stated coefficient.

**Theorem 1.2 (Sharp complete graph lower bound).**

$$\forall m \in \mathbb{N},\; (2 \le m) \Rightarrow (\exists g \in \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{ZeroDivSkew}\left(m\right)\right),\; (\operatorname{skew}\left(\operatorname{Fin}\left(m\right), g\right)) \land ((\operatorname{triangle}\left(\operatorname{Fin}\left(m\right), g, 1\right)) \land (\forall phi \in \operatorname{Fin}\left(m\right) \to \operatorname{ZeroDivSkew}\left(m\right),\; \exists i \in \operatorname{Fin}\left(m\right),\; \exists j \in \operatorname{Fin}\left(m\right),\; (i \neq j) \land (\frac{\operatorname{real}\left(m\right)-2}{\operatorname{real}\left(m\right)} \le \operatorname{error}\left(g, phi, i, j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.completeGraph_banach_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The space ZeroDivSkew(m) consists of real m by m skew matrices whose row sums vanish, viewed as a real submodule with the supremum norm on matrix entries. Its finite dimension implies completeness. A signed triangle has entries of absolute value at most one, is skew and has zero row sums. Fix a root o and assign to (i,j) the signed triangle (o,i,j). The triangle defects are signed triangles. On its own coordinate (i,j), a gain with distinct endpoints has entry one if both endpoints differ from the root and zero otherwise. The sum over all ordered distinct pairs is (m minus one) times (m minus two). The corresponding sum for any potential differences vanishes by skew symmetry and the row sum equations. If every residual norm were smaller than the stated constant, the sum of residuals on their own edge coordinates would be strictly smaller than the gain sum, a contradiction.

**Theorem 1.3 (Midpoint averaging on separated clique sums).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall w \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(w\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , \forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall T \in \operatorname{SimpleGraph}\left(I\right),\; (\operatorname{IsTree}\left(T\right)) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall P \in I \to \operatorname{Set}\left(V\right),\; (\operatorname{cover}\left(V, P\right)) \Rightarrow ((\operatorname{edgeCover}\left(G, P\right)) \Rightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\operatorname{Attach}\left(T, G, P, m\right)) \Rightarrow ((\operatorname{DisjointNonneighbors}\left(T, P\right)) \Rightarrow ((\operatorname{Separated}\left(T, G, P\right)) \Rightarrow (\forall g \in V \to \left(V \to E\right),\; \forall R \in \mathbb{R},\; (0 \le R) \Rightarrow (\forall phi \in I \to \left(V \to E\right),\; (\operatorname{Fit}\left(G, P, g, phi, R\right)) \Rightarrow (\exists Phi \in V \to E,\; \forall x \in V,\; \forall y \in V,\; (\operatorname{Adj}\left(G, x, y\right)) \Rightarrow (\operatorname{error}\left(g, Phi, x, y\right) \le (2-\frac{1}{\operatorname{real}\left(m\right)}) \cdot R))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.separatedCliqueSum_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here S(a,b) is the intersection of the piece vertex sets P(a) and P(b). The cover condition assigns each vertex to a piece, and edgeCover requires the two endpoints of every graph edge to lie in a common piece. Attach requires every tree-edge intersection to be a nonempty clique of size at most m. DisjointNonneighbors requires disjoint pieces for distinct nonadjacent tree vertices. Separated requires, for each piece and any two distinct tree neighbors, that their attachment sets in that piece be disjoint and that no graph edge join these two sets. Fit means that the error on every ordered graph edge internal to its piece is at most R. Integrate along the unique paths from a tree root to shift each piece potential by a constant. For every attachment clique the mean of the difference of the shifted potentials is zero. Every two values of that difference differ in seminorm by at most twice R. Subtracting the mean and omitting the zero self-difference bounds half the mismatch by (one minus the reciprocal of the attachment size) times R. Separation implies each shared vertex belongs to exactly two pieces. Assign it the midpoint of the shifted potentials, and retain the shifted potential at each unshared vertex. On an edge inside a shared clique the residual is the mean of the two fitted residuals. Every other edge has at most one endpoint adjusted, so the radius increases by at most (one minus one over m) times R.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.completeGraph_banach_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.completeGraph_banach_upper_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.separatedCliqueSum_banach_gain_potential`
