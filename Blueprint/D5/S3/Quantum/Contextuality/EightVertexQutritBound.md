# Sharp qutrit bounds for two eight-vertex graphs

## Abstract

The Wagner graph and the rank-five graph of Tamer et al. have greatest real qutrit score three, independence number three, and least dimension of a real contextuality violation four.

All vector spaces and inner products are real. A realization assigns a unit vector to each vertex and makes vectors at adjacent vertices orthogonal. Distinct vertices may have equal vectors, and nonadjacent vertices may be orthogonal. Inner.inner with scalar field ℝ is the real inner product. A natural number annotated as real denotes its real cast.

**Definition 1.1 (The eight vertex labels).**

$$\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex} = \operatorname{Fin}\left(8\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin 8 labels the vertices by the natural numbers from zero through seven.

**Definition 1.2 (Real Euclidean space).**

$$\forall (d: \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.E}\left(d\right) = \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EuclideanSpace ℝ (Fin d) is the real d-dimensional inner product space, including d=0.

**Definition 1.3 (The Wagner graph).**

$$\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.W} = \operatorname{SimpleGraph.fromRel}\left(\lambda (i: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}) \mapsto (\lambda (j: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}) \mapsto ((i, j) \in (\left\{(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0), (0, 4), (1, 5), (2, 6), (3, 7)\right\}: \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}, \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.W` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

Table VI, rank three, specifies the Wagner graph by these twelve pairs. SimpleGraph.fromRel adds the reverse pairs and excludes loops, so the displayed relation defines an undirected simple graph.

**Definition 1.4 (The graph of rank five).**

$$\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.G5} = \operatorname{SimpleGraph.fromRel}\left(\lambda (i: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}) \mapsto (\lambda (j: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}) \mapsto ((i, j) \in (\left\{(0, 3), (0, 5), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (2, 7), (3, 6), (3, 7), (4, 7), (5, 7)\right\}: \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}, \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.G5` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

These are exactly the twelve pairs in row five of Table VI. SimpleGraph.fromRel again makes the relation symmetric and irreflexive. The name G5 refers to its table rank.

**Definition 1.5 (Unit vectors respecting exclusivity).**

$$\forall (d: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)), (\forall (v: (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex} \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Realizes}\left(G, v\right)) \Leftrightarrow ((\forall (i: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}), (\left\lVert v\left(i\right) \right\rVert = 1)) \land (\forall (i: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}), (\forall (j: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}), ((\operatorname{SimpleGraph.Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{Inner.inner}\left(\mathbb{R}, v\left(i\right), v\left(j\right)\right) = 0))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.Realizes` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

Equation (13) imposes unit length at every vertex and orthogonality on every edge. It imposes no converse to edge orthogonality and no injectivity requirement on the vector assignment.

**Definition 1.6 (The squared real overlap).**

$$\forall (d: \mathbb{N}), (\forall (psi: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)), (\forall (x: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)), (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.overlapSq}\left(psi, x\right) = \operatorname{Inner.inner}\left(\mathbb{R}, psi, x\right)^{2})))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.overlapSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any two vectors in the same real Euclidean space, overlapSq raises their inner product to the second power. Neither vector is required to have unit length in this definition.

**Definition 1.7 (The sum of eight overlaps).**

$$\forall (d: \mathbb{N}), (\forall (v: (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex} \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))), (\forall (psi: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)), (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.score}\left(v, psi\right) = \sum_{(i: \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex})} (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.overlapSq}\left(psi, v\left(i\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.score` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

For a realization and a unit state vector, this is the expectation of the sum of the eight rank-one projectors. Equations (12) and (13) maximize that expectation over states and realizations. The function itself is defined for every vector assignment and every state vector.

**Definition 1.8 (A homogeneous bound on every state).**

$$\forall (G: \operatorname{SimpleGraph}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)), (\forall (d: \mathbb{N}), (\forall (c: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.UpperBound}\left(G, d, c\right)) \Leftrightarrow (\forall (v: (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex} \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Realizes}\left(G, v\right)) \Rightarrow (\forall (psi: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)), (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.score}\left(v, psi\right) \le c \cdot \left\lVert psi \right\rVert^{2})))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.UpperBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An upper bound c applies to every realization and every state vector, with the factor ‖ψ‖² retaining homogeneity. For unit ψ the bound is c.

**Definition 1.9 (All scores attained by unit states).**

$$\forall (G: \operatorname{SimpleGraph}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)), (\forall (d: \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.UnitScores}\left(G, d\right) = \{(t: \mathbb{R}) \mid (\exists (v: (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex} \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Realizes}\left(G, v\right)) \land (\exists (psi: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)), ((\left\lVert psi \right\rVert = 1) \land (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.score}\left(v, psi\right) = t)))))\}))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.UnitScores` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

This set collects all real scores obtained from a realization in dimension d and a unit state in that same space. It is the state-expectation formulation of the optimization in Eqs. (12) and (13).

**Definition 1.10 (The dimension-restricted supremum).**

$$\forall (G: \operatorname{SimpleGraph}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)), (\forall (d: \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.eta}\left(G, d\right) = \operatorname{sSup}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.UnitScores}\left(G, d\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.eta` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

The quantity in Eq. (13) is expressed as sSup of UnitScores. Using a supremum defines eta for every natural dimension without assuming that a maximizing realization exists. Attainment in dimension three is stated separately below.

**Definition 1.11 (A score above the independence number).**

$$\forall (G: \operatorname{SimpleGraph}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)), (\forall (d: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.HasViolation}\left(G, d\right)) \Leftrightarrow (\exists (v: (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex} \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right))), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Realizes}\left(G, v\right)) \land (\exists (psi: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)), ((\left\lVert psi \right\rVert = 1) \land ((\operatorname{SimpleGraph.indepNum}\left(G\right): \mathbb{R}) < \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.score}\left(v, psi\right))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.HasViolation` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

A violation is an attained unit-state score strictly above SimpleGraph.indepNum, the noncontextual bound. Equation (25) asks for the minimum dimension with such a violation; its exact minimum for the two graphs is stated using IsLeast below.

**Definition 1.12 (The six sharp-bound conclusions).**

$$\forall (G: \operatorname{SimpleGraph}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Vertex}\right)), ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Settled}\left(G\right)) \Leftrightarrow ((\operatorname{SimpleGraph.indepNum}\left(G\right) = 3) \land ((\forall (d: \mathbb{N}), ((d \le 3) \Rightarrow (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.UpperBound}\left(G, d, 3\right)))) \land ((\operatorname{IsGreatest}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.UnitScores}\left(G, 3\right), 3\right)) \land ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.eta}\left(G, 3\right) = 3) \land ((3 < \operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.eta}\left(G, 4\right)) \land (\operatorname{IsLeast}\left(\{(d: \mathbb{N}) \mid (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.HasViolation}\left(G, d\right))\}, 4\right))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.Settled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independence number is three. Every natural dimension at most three has the homogeneous upper bound three. Three is the greatest attained unit score in dimension three, and the dimension-three supremum equals three. The dimension-four supremum is strictly larger than three. Finally, four is the least natural dimension admitting an attained violation. IsGreatest includes both attainment and an upper bound; IsLeast includes both a violation at four and exclusion of all smaller dimensions.

**Definition 1.13 (The proposition for both graphs).**

$$(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.claim}) \Leftrightarrow ((\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Settled}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.W}\right)) \land (\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.Settled}\left(\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.G5}\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EightVertexQutritBound.claim` (`✓ std3`).

*Citation.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

Section IV calls for an independent three-dimensional upper bound for the Wagner graph. Table V(a) gives qutrit value three and minimum dimension four for both the Wagner graph and the graph of rank five, with a dagger marking those dimension conclusions as numerical. This proposition states the exact conclusions for both graphs, including attainment and the bounds in every dimension at most three.

**Theorem 1.14 (Qutrit value three and minimum violation dimension four).**

$$\operatorname{D5.S3.Quantum.Contextuality.EightVertexQutritBound.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/EightVertexQutritBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/tamer-et-al-2026-eight-vertex-qutrit-dimension` (proved) by `D5/S3/Quantum/Contextuality/EightVertexQutritBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tamer-et-al-2026-eight-vertex-qutrit-dimension","declaration_gid":"D5/S3/Quantum/Contextuality/EightVertexQutritBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Uğur Tamer, Berke Ünal, Alper Dizdar, Zafer Gedik, Özgür E. Müstecaplıoğlu (2026). *The Quad-C5 Graph: Maximum Contextuality Gap on Eight Vertices*. URL: <https://arxiv.org/abs/2605.12828v3>.

*Commentary.*

In ℝ³, a cycle of four unit vectors with successive orthogonality forces one pair of opposite vectors to agree up to sign: if one opposite pair is linearly independent, the other pair lies in its one-dimensional orthogonal complement. Applying this fact to the squares of either graph yields, for every realization, an edge with endpoints i and j such that the score for every ψ is 2‖ψ‖² + ⟨ψ,v_i⟩² + ⟨ψ,v_j⟩². Parseval replaces the sum of the three squared overlaps of an orthonormal basis by ‖ψ‖², and Bessel bounds the last two terms by ‖ψ‖². Thus every score is at most 3‖ψ‖². Isometric embedding into ℝ³ gives the same bound in smaller dimensions.

With e₀,e₁,e₂ the standard orthonormal basis of ℝ³, the vertex assignments (e₀,e₁,e₂,e₀,e₁,e₀,e₁,e₂) for W and (e₂,e₀,e₀,e₀,e₁,e₁,e₁,e₂) for G5 respect every edge. Taking ψ=e₀ attains score three in each case. Enumerating the independent subsets gives independence number three; maximum independent sets are {0,3,5} for W and {1,2,3} for G5.

In ℝ⁴, normalize the eight W vectors (20,15,0,0), (9,−12,−12,16), (12,16,9,12), (20,−15,0,0), (0,0,−15,20), (16,12,12,9), (−12,9,16,−12), (0,0,15,20) and the state (4,0,0,3). Their unit-state score is 49449/15625. For G5, normalize (19,5,−13,0), (−2,5,29,−15), (0,0,0,−1), (8,−20,4,−15), (2,31,1,12), (2,−5,1,0), (−5,−2,0,0), (−1,0,2,0) and the state (1,2,−2,1). The score is 846537181/276109725. Every edge has zero inner product in both assignments, and both scores exceed three. These realizations, together with the sharp qutrit bounds, establish the real minimum dimension four indicated in §IV and Table V(a).

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.E`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.G5`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.HasViolation`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.Realizes`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.Settled`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.UnitScores`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.UpperBound`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.Vertex`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.W`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.eta`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.overlapSq`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/EightVertexQutritBound.score`
