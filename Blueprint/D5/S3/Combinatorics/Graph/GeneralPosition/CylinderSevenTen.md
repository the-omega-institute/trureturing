# Mobile general position on two exceptional cylinders

## Abstract

The mobile general position number of the seven-cycle and ten-cycle cylinders is four at every height at least five.

Vertices are pairs in Fin r × Fin s. The cycle coordinate is numbered from zero modulo r, and the path coordinate is numbered from zero to s−1. Finite sets record occupied vertices, with one robot at each vertex. Distances are SimpleGraph.dist. The cylinders in the theorem are finite and connected.

**Definition 1.1 (A vertex between two others).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (u : V), \forall (v : V), \forall (w : V), \operatorname{OnGeodesic}\left(G, u, v, w\right) = \left(\operatorname{SimpleGraph.dist}\left(G, u, v\right) + \operatorname{SimpleGraph.dist}\left(G, v, w\right) = \operatorname{SimpleGraph.dist}\left(G, u, w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.OnGeodesic` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 1.1, PDF page 3: “The distance between vertices u, v ∈ V(G) is the length of a shortest u, v-path in G.” On these connected graphs, equality of the two distances through v with the endpoint distance says that v lies on a shortest path from u to w.

**Definition 1.2 (General position).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), \operatorname{IsGeneralPosition}\left(G, S\right) = (\forall (u : V), u \in S \Rightarrow \forall (v : V), v \in S \Rightarrow \forall (w : V), w \in S \Rightarrow \left(u \ne v \Rightarrow \left(v \ne w \Rightarrow \left(u \ne w \Rightarrow \neg (\operatorname{OnGeodesic}\left(G, u, v, w\right))\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.IsGeneralPosition` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 1.1, PDF page 3: “If S ⊆ V(G) has the property that no three vertices of S lie on a common shortest path of G, then we say that S is a general position set of G.” The three vertices are pairwise distinct, and each belongs to the occupied finite set.

**Definition 1.3 (One legal robot move).**

$$\forall (V : Type), [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), \forall (T : \operatorname{Finset}\left(V\right)), \operatorname{LegalMove}\left(G, S, T\right) = (\exists (u : V), u \in S \land \exists (v : V), \neg (v \in S) \land \left(\operatorname{SimpleGraph.Adj}\left(G, u, v\right) \land \left(T = \operatorname{insert}\left(v, \operatorname{Finset.erase}\left(S, u\right)\right) \land \operatorname{IsGeneralPosition}\left(G, T\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.LegalMove` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 1.1, PDF pages 3–4: “If a robot is located at a vertex u and u ∼ v, then we indicate the movement of the robot from u to v along the edge uv by u ⇝ v and refer to this as a move.” “If a robot is stationed at a vertex u of S, then the move u ⇝ v is called a legal move if i) v ∉ S (thereby avoiding having more than one robot per vertex at any stage) and ii) the new set (S ∖ {u}) ∪ {v} is also a general position set.” The target is insert v (S.erase u).

**Definition 1.4 (A finite traversal of the graph).**

$$\forall (V : Type), [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (S : \operatorname{Finset}\left(V\right)), \operatorname{IsMobile}\left(G, S\right) = \left(\operatorname{IsGeneralPosition}\left(G, S\right) \land \exists (n : \mathrm{Nat}), \exists (c : \operatorname{Fin}\left(n + 1\right) \to \operatorname{Finset}\left(V\right)), c\left(0\right) = S \land \left((\forall (i : \operatorname{Fin}\left(n\right)), \operatorname{LegalMove}\left(G, c\left(\operatorname{Fin.castSucc}\left(i\right)\right), c\left(\operatorname{Fin.succ}\left(i\right)\right)\right)) \land (\forall (x : V), \exists (i : \operatorname{Fin}\left(n + 1\right)), x \in c\left(i\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.IsMobile` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 1.1, PDF page 4: “A configuration of robots on a general position set of G is called a mobile general position set if there is a sequence of legal moves starting from S such that every vertex of G is visited at least once by some robot.” A sequence has n+1 configurations indexed by Fin (n+1); each consecutive pair is a legal move, and their union contains every vertex.

**Definition 1.5 (The mobile general position number).**

$$\forall (V : Type), [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{mobGP}\left(G\right) = \operatorname{sSup}\left(\{k : \mathrm{Nat} \mid \exists (S : \operatorname{Finset}\left(V\right)), \operatorname{Finset.card}\left(S\right) = k \land \operatorname{IsMobile}\left(G, S\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.mobGP` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 1.1, PDF page 4: “The mobile general position number, written Mobgp(G), is the largest number of robots in a mobile general position set of G.” The natural-number supremum is taken over the cardinalities of finite mobile sets; for the finite cylinders it is attained and bounded by the vertex count.

**Definition 1.6 (The Cartesian product graph).**

$$\forall (r : \mathrm{Nat}), \forall (s : \mathrm{Nat}), \operatorname{cylinder}\left(r, s\right) = \operatorname{SimpleGraph.boxProd}\left(\operatorname{cycleGraph}\left(r\right), \operatorname{pathGraph}\left(s\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.cylinder` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 2, PDF page 4: “Recall that the Cartesian product G □ H of graphs G and H satisfies V(G □ H) = V(G) × V(H) and (g, h)(g′, h′) ∈ E(G □ H) if either gg′ ∈ E(G) and h = h′, or g = g′ and hh′ ∈ E(H).” Here the factors are cycleGraph r and pathGraph s.

**Definition 1.7 (The two remaining cylinder cases).**

$$claim = (\forall (s : \mathrm{Nat}), 5 \le s \Rightarrow \left(\operatorname{mobGP}\left(\operatorname{cylinder}\left(7, s\right)\right) = 4 \land \operatorname{mobGP}\left(\operatorname{cylinder}\left(10, s\right)\right) = 4\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.claim` (`✓ std3`).

*Citation.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Section 3, PDF page 15, after Proposition 3.7: “Hence, the only unknown values are Mobgp(C₇ □ Pₛ) and Mobgp(C₁₀ □ Pₛ) for s ≥ 5. We conjecture that the answer is four in these cases.” The parameter s counts the vertices of the path. Both asserted values are four for every natural s at least five.

**Theorem 1.8 (Both values are four).**

$$\forall (s : \mathrm{Nat}), 5 \le s \Rightarrow \left(\operatorname{mobGP}\left(\operatorname{cylinder}\left(7, s\right)\right) = 4 \land \operatorname{mobGP}\left(\operatorname{cylinder}\left(10, s\right)\right) = 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.result` (`✓ std3`). ∎

*Resolves.* `Problems/klavzar-et-al-2025-mobile-general-position-cylinders` (proved) by `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klavzar-et-al-2025-mobile-general-position-cylinders","declaration_gid":"D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavžar; Aditi Krishnakumar; Dorota Kuziak; Ethan Shallcross; James Tuite; Ismael G. Yero (2026). *Moving through Cartesian products, coronas and joins in general position*. DOI: [10.1016/j.dam.2025.10.041](https://doi.org/10.1016/j.dam.2025.10.041). URL: <https://arxiv.org/abs/2505.00535>.

*Commentary.*

Five robots in general position have distinct path coordinates. In row order their cycle coordinates form an arithmetic progression with step ±2 on the seven-cycle or ±3 on the ten-cycle. A legal move of five robots cannot change a cycle coordinate, so an unoccupied column remains unvisited. No six vertices are in general position. Four robots traverse two consecutive rows by four horizontal moves and their rotations; four vertical moves shift this traversal to the next row pair. The upper bound holds at every height, and the four-robot construction works at every height at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.IsGeneralPosition`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.IsMobile`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.LegalMove`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.OnGeodesic`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.cylinder`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.mobGP`
- Truth anchor: `D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.result`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle](../Walks/MatchingCliqueCycle.md)
