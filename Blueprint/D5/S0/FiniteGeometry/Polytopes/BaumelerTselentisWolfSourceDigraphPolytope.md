# The Source-Digraph Polytope

## Abstract

Trivial and kefalopoda inequalities describe every source-digraph polytope.

**Definition 1.1 (A source vertex).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Finset}\left(\{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\}\right), \operatorname{HasSource}\left(A\right)\iff\exists i: \operatorname{Fin}\left(n\right), \forall e: \{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\}, e\in A\implies \operatorname{Prod}.\operatorname{snd}\left(\operatorname{val}\left(e\right)\right)\neq i$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.HasSource` (`✓ std3`).

*Citation.* Ämin Baumeler; Eleftherios-Ermis Tselentis; Stefan Wolf (2025). *Graphical Tests of Causality*. DOI: [10.1016/j.jlamp.2026.101133](https://doi.org/10.1016/j.jlamp.2026.101133). URL: <https://arxiv.org/abs/2511.22552v1>.

*Commentary.*

Page 17, Theorem 3: “The set of digraphs Γ(P_n^causal) is the set of all digraphs on n vertices with at least one source vertex:”. Vertices are Fin n; arcs are ordered pairs of distinct vertices. A source is a vertex that is never the receiver of an arc in A.

**Definition 1.2 (The convex hull of source digraphs).**

$$\forall n: \mathbb{N}, \operatorname{sourcePolytope}\left(n\right)=\operatorname{convexHull}\left(\mathbb{R}, \{x: \{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\} \to \mathbb{R}\mid\exists A: \operatorname{Finset}\left(\{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\}\right), \operatorname{HasSource}\left(A\right)\land x=(\operatorname{fun} e: \{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\}\mapsto \operatorname{if} e\in A \operatorname{then} 1 \operatorname{else} 0)\}\right)$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.sourcePolytope` (`✓ std3`).

*Citation.* Ämin Baumeler; Eleftherios-Ermis Tselentis; Stefan Wolf (2025). *Graphical Tests of Causality*. DOI: [10.1016/j.jlamp.2026.101133](https://doi.org/10.1016/j.jlamp.2026.101133). URL: <https://arxiv.org/abs/2511.22552v1>.

*Commentary.*

Page 17, Definition 8: “The polytope of source digraphs is Q_n^src := conv(Γ(P_n^causal)).” Section 2, page 6: “For a digraph D with V(D) = [n], we use α(D) ∈ {0, 1}^{n(n−1)} for the adjacency vector with α(D)_{i,j} = 1 ⇔ i j ∈ A(D).”. Finite arc sets describe all loopless digraphs, including the empty digraph; each adjacency coordinate is one for a present arc and zero otherwise. The convex hull is over the real numbers.

**Definition 1.3 (The three inequality families).**

$$\forall n: \mathbb{N}, \operatorname{kefalopodaPolytope}\left(n\right)=\{x: \{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\} \to \mathbb{R}\mid (\forall e: \{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\}, 0\leq \operatorname{x}\left(e\right))\land(3\leq n\implies \forall e: \{p: \operatorname{Fin}\left(n\right)\times \operatorname{Fin}\left(n\right)\mid\operatorname{Prod}.\operatorname{fst}\left(p\right)\neq \operatorname{Prod}.\operatorname{snd}\left(p\right)\}, \operatorname{x}\left(e\right)\leq 1)\land(\forall f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right), \forall hf: (\forall i: \operatorname{Fin}\left(n\right), \operatorname{f}\left(i\right)\neq i), \sum_{i: \operatorname{Fin}\left(n\right)}\operatorname{x}\left(\langle(\operatorname{f}\left(i\right),i),\operatorname{hf}\left(i\right)\rangle\right)\leq (n: \mathbb{R})-1)\}$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.kefalopodaPolytope` (`✓ std3`).

*Citation.* Ämin Baumeler; Eleftherios-Ermis Tselentis; Stefan Wolf (2025). *Graphical Tests of Causality*. DOI: [10.1016/j.jlamp.2026.101133](https://doi.org/10.1016/j.jlamp.2026.101133). URL: <https://arxiv.org/abs/2511.22552v1>.

*Commentary.*

Page 24, Definition 13: “The polytope Q̃_n^src ⊆ ℝ^{n(n−1)} is the set of vectors that satisfy the following inequalities:” (58)–(60). These are coordinate nonnegativity, coordinate upper bounds for n ≥ 3, and one sum at most n − 1 for every fixed-point-free function. Page 17, Definition 9: “For any function f : [n] → [n] without fixed-points, i.e, with ∀i : f(i) ≠ i, the kefalopoda κ_f is” V(κ_f) = [n], A(κ_f) = {f(i) i | i ∈ [n]}. Thus f(i) is the sender and i the receiver; all sums count vertices once. The cast of n in the last bound is real.

**Definition 1.4 (The identity in every dimension).**

$$\operatorname{claim}\iff (\forall n: \mathbb{N}, 2\leq n\implies\operatorname{kefalopodaPolytope}\left(n\right)=\operatorname{sourcePolytope}\left(n\right))$$

*Formalization.* `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.claim` (`✓ std3`).

*Citation.* Ämin Baumeler; Eleftherios-Ermis Tselentis; Stefan Wolf (2025). *Graphical Tests of Causality*. DOI: [10.1016/j.jlamp.2026.101133](https://doi.org/10.1016/j.jlamp.2026.101133). URL: <https://arxiv.org/abs/2511.22552v1>.

*Commentary.*

Page 24, after Definition 13: “We know that Q̃_n^src = Q_n^src for n ≤ 4. In general, this identity is unsolved.” The proposition asserts the identity for every natural n ≥ 2, with the three inequality families displayed above.

**Theorem 1.5 (The source-digraph polytope identity).**

$$\forall n: \mathbb{N}, 2\leq n\implies\operatorname{kefalopodaPolytope}\left(n\right)=\operatorname{sourcePolytope}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.result` (`✓ std3`). ∎

*Resolves.* `Problems/baumeler-tselentis-wolf-2025-source-digraph-polytope` (proved) by `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baumeler-tselentis-wolf-2025-source-digraph-polytope","declaration_gid":"D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ämin Baumeler; Eleftherios-Ermis Tselentis; Stefan Wolf (2025). *Graphical Tests of Causality*. DOI: [10.1016/j.jlamp.2026.101133](https://doi.org/10.1016/j.jlamp.2026.101133). URL: <https://arxiv.org/abs/2511.22552v1>.

*Commentary.*

The kefalopoda sums bound the sum of the largest incoming coordinates by n − 1. Their complementary slacks give probabilities for the source vertex. Zeroing that source column and rescaling the others expresses each point as a convex mixture of fixed-source unit boxes. Each box is the convex hull of its zero-one source digraphs. For n = 2 the kefalopoda inequality and nonnegativity already imply the coordinate upper bounds.

## References

- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.HasSource`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.claim`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.kefalopodaPolytope`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.result`
- Truth anchor: `D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope.sourcePolytope`
