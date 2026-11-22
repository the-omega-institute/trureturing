# Open Problem 14.2(i): no uniform left gap at −2

## Abstract

Connected cographs have distance eigenvalues arbitrarily close to −2 from below.

**Definition 1.1 (Vertices of the counterexample family).**

$$\forall r \in \mathbb{N},\; \operatorname{Vertex}\left(r\right) = \operatorname{Sum}\left(\operatorname{Bool}, (\operatorname{Fin}\left(r\right) \times \operatorname{Bool})\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two Boolean vertices on the left are the universal vertex (false) and the initially isolated vertex (true). On the right, an index selects one of the matching edges, and a Boolean selects its endpoint.

**Definition 1.2 (Join with a singleton and a matching).**

$$\forall r \in \mathbb{N},\; \forall a \in \operatorname{Bool},\; \forall b \in \operatorname{Bool},\; ((\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{family}\left(r\right), \operatorname{Sum}.\operatorname{inl}\left(a\right), \operatorname{Sum}.\operatorname{inl}\left(b\right)\right)) \iff (a \neq b)) \land ((\forall j \in \operatorname{Fin}\left(r\right),\; (\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{family}\left(r\right), \operatorname{Sum}.\operatorname{inl}\left(a\right), \operatorname{Sum}.\operatorname{inr}\left((j, b)\right)\right)) \iff (a = \operatorname{false})) \land ((\forall i \in \operatorname{Fin}\left(r\right),\; (\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{family}\left(r\right), \operatorname{Sum}.\operatorname{inr}\left((i, a)\right), \operatorname{Sum}.\operatorname{inl}\left(b\right)\right)) \iff (b = \operatorname{false})) \land (\forall i \in \operatorname{Fin}\left(r\right),\; \forall j \in \operatorname{Fin}\left(r\right),\; (\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{family}\left(r\right), \operatorname{Sum}.\operatorname{inr}\left((i, a)\right), \operatorname{Sum}.\operatorname{inr}\left((j, b)\right)\right)) \iff ((i = j) \land (a \neq b)))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.family` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The graph is K₁ joined to the disjoint union of one singleton and r independent copies of K₂. Distinct singleton vertices are adjacent. Across the sum, only the universal vertex is adjacent to matching endpoints. Matching endpoints are adjacent exactly when their indices agree and their Booleans differ.

**Definition 1.3 (No induced four-vertex path).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{P4Free}\left(G\right) \iff \operatorname{IsEmpty}\left(\operatorname{SimpleGraph}.\operatorname{Embedding}\left(\operatorname{SimpleGraph}.\operatorname{pathGraph}\left(4\right), G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.P4Free` (`✓ std3`).

*Citation.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Section 1, printed p. 2, defines a cograph as “a finite simple graph containing no induced path on four vertices P₄.” A graph embedding preserves and reflects adjacency, so the predicate excludes exactly induced copies of the native four-vertex path.

**Definition 1.4 (Shortest-path distance matrix).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall x \in V,\; \forall y \in V,\; \operatorname{distanceMatrix}\left(G, x, y\right) = (\operatorname{SimpleGraph}.\operatorname{dist}\left(G, x, y\right): \mathbb{R})$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.distanceMatrix` (`✓ std3`).

*Citation.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The real matrix casts the native shortest-path edge count, including the diagonal zero. For a connected cograph on at least two vertices, Proposition 2.6 (printed p. 5 of arXiv:2611.06981v1) gives diameter at most two. Section 6 (printed p. 14) states the identity D = 2J − 2I − A.

**Theorem 1.5 (An eigenvalue in every open left neighborhood).**

$$\forall epsilon \in \mathbb{R},\; (0 < epsilon) \Rightarrow (\exists r \in \mathbb{N},\; (0 < r) \land (\exists lambda \in \mathbb{R},\; (-2 - epsilon < lambda) \land ((lambda < -2) \land ((\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{family}\left(r\right)\right)) \land ((\operatorname{P4Free}\left(\operatorname{family}\left(r\right)\right)) \land (\operatorname{Module}.\operatorname{End}.\operatorname{HasEigenvalue}\left(\operatorname{Matrix}.\operatorname{mulVecLin}\left(\operatorname{distanceMatrix}\left(\operatorname{family}\left(r\right)\right)\right), lambda\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.registered_family_counters_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

The universal vertex gives connectedness and a walk of length two between distinct nonadjacent vertices. Each vertex of an induced P₄ has a nonneighbor among the other three, so the path avoids the universal vertex. The remaining vertices have at most one neighbor each. On the orbit-constant subspace, the distance quotient has rows (0, 1, 2r), (1, 0, 4r), and (1, 2, 4r−3). For t = λ + 2 its characteristic determinant is (t+1)(t−1)(t−3) + (6−4t)rt. At t = 0 this is 3. With r = q > 0 and t = −1/q it is −((1+1/q)³+2). Continuity gives a root in the strict interior. Choose 1/q < ε and lift a nonzero quotient kernel vector to the three nonempty orbits.

**Definition 1.6 (The proposed uniform gap).**

$$\operatorname{claim} = (\exists epsilon \in \mathbb{R},\; (0 < epsilon) \land (\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow ((\operatorname{P4Free}\left(G\right)) \Rightarrow (\forall lambda \in \mathbb{R},\; (\operatorname{Module}.\operatorname{End}.\operatorname{HasEigenvalue}\left(\operatorname{Matrix}.\operatorname{mulVecLin}\left(\operatorname{distanceMatrix}\left(G\right)\right), lambda\right)) \Rightarrow (\neg ((-2 - epsilon < lambda) \land (lambda < -2)))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.claim` (`✓ std3`).

*Citation.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Open Problem 14.2(i), printed p. 22, asks “Is there ε > 0 such that (−2 − ε, −2) contains no distance eigenvalue of any connected cograph?” The graph ranges over all connected finite simple graphs with no induced four-vertex path. A real eigenvalue means that the distance matrix sends some nonzero real vector v to λv. The same positive ε must work for every graph, and both inequalities are strict.

**Theorem 1.7 (Refutation of the uniform gap).**

$$\neg (\exists epsilon \in \mathbb{R},\; (0 < epsilon) \land (\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow ((\operatorname{P4Free}\left(G\right)) \Rightarrow (\forall lambda \in \mathbb{R},\; (\operatorname{Module}.\operatorname{End}.\operatorname{HasEigenvalue}\left(\operatorname{Matrix}.\operatorname{mulVecLin}\left(\operatorname{distanceMatrix}\left(G\right)\right), lambda\right)) \Rightarrow (\neg ((-2 - epsilon < lambda) \land (lambda < -2)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/manna-mandal-tura-2026-cograph-distance-left-gap` (refuted) by `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"manna-mandal-tura-2026-cograph-distance-left-gap","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

For every proposed ε, the joined matching family supplies a finite connected cograph and a real distance eigenvalue strictly inside the proposed interval. Open Problem 14.2(ii) asks separately about attaining the multiplicity bound.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.P4Free`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.Vertex`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.distanceMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.family`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.registered_family_counters_gap`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.result`
