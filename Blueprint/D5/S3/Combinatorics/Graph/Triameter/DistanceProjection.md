# Distance projection and packing comparison for triameter

## Abstract

Surjective distance projections transfer distance-packing estimates to connected graphs.

**Definition 1.1 (EvenLegTriangle.Vertex).**

$$\forall (q: \operatorname{Fin}(3) \to \mathbb{N}), \operatorname{EvenLegTriangle.Vertex}(q) = \Sigma (i: \operatorname{Fin}(3)) \operatorname{Fin}(2\cdot\operatorname{q}(i)+1)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.Vertex` (`✓ std3`).

*Citation.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

This gives leg and depth coordinates for the vertices of U(2q₀, 2q₁, 2q₂) in §2.1. A vertex is a dependent pair of a leg i and a depth from zero through 2q(i).

**Definition 1.2 (EvenLegTriangle.H).**

$$\forall (q: \operatorname{Fin}(3) \to \mathbb{N}) (x: \operatorname{EvenLegTriangle.Vertex}(q)) (y: \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{SimpleGraph.Adj}(\operatorname{EvenLegTriangle.H}(q), x, y) \Leftrightarrow (\operatorname{Sigma.fst}(x) = \operatorname{Sigma.fst}(y) \land (\operatorname{Fin.val}(\operatorname{Sigma.snd}(x))+1 = \operatorname{Fin.val}(\operatorname{Sigma.snd}(y)) \lor \operatorname{Fin.val}(\operatorname{Sigma.snd}(y))+1 = \operatorname{Fin.val}(\operatorname{Sigma.snd}(x)))) \lor (\operatorname{Sigma.fst}(x) \neq \operatorname{Sigma.fst}(y) \land \operatorname{Fin.val}(\operatorname{Sigma.snd}(x)) = 0 \land \operatorname{Fin.val}(\operatorname{Sigma.snd}(y)) = 0)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.H` (`✓ std3`).

*Citation.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

This is the triangle with attached paths U(2q₀, 2q₁, 2q₂) from §2.1. Edges join consecutive depths on each leg and join every two distinct roots.

**Definition 1.3 (perimeter).**

$$\forall (V: \operatorname{Type}) (G: \operatorname{SimpleGraph}(V)) (a: \operatorname{Fin}(3) \to V), \operatorname{perimeter}(G, a) = \operatorname{SimpleGraph.dist}(G, \operatorname{a}(0), \operatorname{a}(1))+\operatorname{SimpleGraph.dist}(G, \operatorname{a}(0), \operatorname{a}(2))+\operatorname{SimpleGraph.dist}(G, \operatorname{a}(1), \operatorname{a}(2))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.perimeter` (`✓ std3`).

*Citation.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

This is the perimeter of an ordered triple from §2.2. Each SimpleGraph.dist term counts the edges of a shortest walk when its endpoints are reachable.

**Definition 1.4 (triameter).**

$$\forall (V: \operatorname{Type}) [\operatorname{Fintype}(V)] (G: \operatorname{SimpleGraph}(V)), \operatorname{triameter}(G) = \operatorname{Finset.sup}(\operatorname{Finset.univ}, \operatorname{perimeter}(G))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter` (`✓ std3`).

*Citation.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

This is the triameter of §2.2, with the supremum taken over every function Fin 3 → V. Triples can contain repeated vertices. The supremum is zero on an empty vertex type.

**Theorem 1.5 (Independence upper bound for triameter).**

$$\forall (V: \operatorname{Type}) [\operatorname{Fintype}(V)] (G: \operatorname{SimpleGraph}(V)), \operatorname{G.Connected} \longrightarrow \operatorname{triameter}(G)+1 \le 4\cdot\operatorname{SimpleGraph.indepNum}(G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter_le_indepNum` (`✓ std3`). ∎

*Citation.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

Corollary 5.1, inequality (5), gives this bound at orders at least three. At connected orders one and two, the triameters are zero and two respectively, and both independence numbers are one. A maximizing triple admits a surjective distance projection onto three legs with a point or triangular centre. Lifting a packing of the model gives a packing of G. At distance threshold one, packings of G are independent sets.

**Theorem 1.6 (Even-leg projection at independence equality).**

$$\forall (V: \operatorname{Type}) [\operatorname{Fintype}(V)] (G: \operatorname{SimpleGraph}(V)), \operatorname{G.Connected} \longrightarrow (\operatorname{triameter}(G) = 4\cdot\operatorname{SimpleGraph.indepNum}(G)-1) \longrightarrow \exists (q: \operatorname{Fin}(3) \to \mathbb{N}) (f: V \to \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{SimpleGraph.indepNum}(G) = \operatorname{q}(0)+\operatorname{q}(1)+\operatorname{q}(2)+1 \land \operatorname{Function.Surjective}(f) \land (\forall x y, \operatorname{SimpleGraph.Adj}(G, x, y) \longrightarrow \operatorname{f}(x) = \operatorname{f}(y) \lor \operatorname{SimpleGraph.Adj}(\operatorname{EvenLegTriangle.H}(q), \operatorname{f}(x), \operatorname{f}(y))) \land (\forall u v, \operatorname{SimpleGraph.Adj}(\operatorname{EvenLegTriangle.H}(q), u, v) \longrightarrow \exists x y, \operatorname{SimpleGraph.Adj}(G, x, y) \land \operatorname{f}(x) = u \land \operatorname{f}(y) = v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.k1_equality_projection` (`✓ std3`). ∎

*Citation.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

The equality part of the proof of Theorem 1.1 at k = 1 forces a triangular centre and leg lengths 2q(i) in the canonical model of §3. Lemma 3.2 supplies the surjective non-expanding projection and the lift of every model edge. Section 2.1 expresses non-expansion as the edge-or-collapse condition. Equality cannot occur at connected orders one and two.

**Theorem 1.7 (Triameter lower bound from lifting the three feet).**

$$\forall (V: \operatorname{Type}) [\operatorname{Fintype}(V)] (G: \operatorname{SimpleGraph}(V)), \operatorname{G.Connected} \longrightarrow \forall (q: \operatorname{Fin}(3) \to \mathbb{N}) (f: V \to \operatorname{EvenLegTriangle.Vertex}(q)), \operatorname{Function.Surjective}(f) \longrightarrow (\forall x y, \operatorname{SimpleGraph.Adj}(G, x, y) \longrightarrow \operatorname{f}(x) = \operatorname{f}(y) \lor \operatorname{SimpleGraph.Adj}(\operatorname{EvenLegTriangle.H}(q), \operatorname{f}(x), \operatorname{f}(y))) \longrightarrow 4\cdot(\operatorname{q}(0)+\operatorname{q}(1)+\operatorname{q}(2))+3 \le \operatorname{triameter}(G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter_ge_of_evenLegTriangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Artem Hak and Sergiy Kozerenko (2026). *Triameter, distance packings, and vertex connectivity*. DOI: [10.48550/arXiv.2611.17259](https://doi.org/10.48550/arXiv.2611.17259). URL: <https://arxiv.org/html/2611.17259v1#S7.p2.1>.

*Commentary.*

Choose preimages of the three feet under the surjective edge map. Walks between those preimages have length at least the distance between the corresponding feet. The sum of the foot distances from Lemma 2.5(2) gives the displayed lower bound for an arbitrary surjection satisfying the stated edge condition.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.H`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.k1_equality_projection`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.perimeter`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter_ge_of_evenLegTriangle`
- Truth anchor: `D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter_le_indepNum`
