# Non-chordal graphs with unstable restricted clique polynomials

## Abstract

For every r ≥ 1, the join of a complete graph on max(r−2,0) vertices with a four-cycle is r-connected, K_{r+3}-free and non-chordal. Marking one cycle vertex gives a clique polynomial with a zero in the product of the upper half-planes.

**Definition 1.1 (The restricted clique polynomial).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (B : \operatorname{Finset}\left(V\right)), \forall (x : \mathbb{C}), \forall (y : \mathbb{C}), \operatorname{C_{B}}\left(G, B, x, y\right) = \sum_{K \in \operatorname{Finset.filter}\left((\lambda (K : \operatorname{Finset}\left(V\right)), \operatorname{SimpleGraph.IsClique}\left(G, (K : \operatorname{Set}\left(V\right))\right)), \operatorname{Finset.powerset}\left((\operatorname{Finset.univ} : \operatorname{Finset}\left(V\right))\right)\right)} x^{\operatorname{Finset.card}\left(K\right)} \cdot y^{\operatorname{Finset.card}\left(\operatorname{Finset.inter}\left(K, B\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.C_B` (`✓ std3`).

*Citation.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

Definition 2.1, page 4: "For G=(V,E) and B ⊆ V, define" C_B(G;x,y) := ∑_{K ⊆ V, K clique} x^{|K|} y^{|K ∩ B|}. Cliques are Mathlib SimpleGraph.IsClique on the set underlying a Finset. Finset.univ.powerset.filter enumerates every clique once, including the empty clique, which contributes 1 as in Example 2.3. The complex-valued function is evaluation of this real-coefficient polynomial.

**Definition 1.2 (Real stability).**

$$\forall (f : \mathbb{C} \to \left(\mathbb{C} \to \mathbb{C}\right)), (\operatorname{RealStable}\left(f\right)) \Leftrightarrow ((\exists (x : \mathbb{C}), \exists (y : \mathbb{C}), f\left(x, y\right) \ne 0) \land (\forall (x : \mathbb{C}), \forall (y : \mathbb{C}), (0 < \operatorname{Complex.im}\left(x\right)) \Rightarrow ((0 < \operatorname{Complex.im}\left(y\right)) \Rightarrow (f\left(x, y\right) \ne 0))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.RealStable` (`✓ std3`).

*Citation.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

Definition 2.4, page 4: "A polynomial f(x,y) ∈ ℝ[x,y] is real stable if it is not identically zero and" f(x,y) ≠ 0 "for all (x,y) ∈ ℂ² such that Im(x) > 0 and Im(y) > 0." Here RealStable is this evaluation predicate on a function ℂ → ℂ → ℂ. It is applied to C_B, whose coefficients are real nonnegative integers. The first conjunct states that the function is not identically zero.

**Definition 1.3 (Vertex connectivity).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (r : \mathbb{N}), (\operatorname{RConnected}\left(G, r\right)) \Leftrightarrow ((r < \operatorname{Fintype.card}\left(V\right)) \land (\forall (S : \operatorname{Finset}\left(V\right)), (\operatorname{Finset.card}\left(S\right) < r) \Rightarrow (\operatorname{SimpleGraph.Connected}\left(\operatorname{SimpleGraph.induce}\left(G, \{v | \neg (v \in S)\}\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.RConnected` (`✓ std3`).

*Citation.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

Definition 4.2, page 7: "A graph is r-connected if removal of fewer than r vertices leaves it connected." The finite graph also has more than r vertices, the standard vertex-connectivity size convention. Deletion is Mathlib SimpleGraph.induce on the set of vertices outside S; connectedness is SimpleGraph.Connected.

**Definition 1.4 (A chord of a closed walk).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (v : V), \forall (p : \operatorname{SimpleGraph.Walk}\left(G, v, v\right)), (\operatorname{HasChord}\left(p\right)) \Leftrightarrow (\exists (i : \operatorname{Fin}\left(\operatorname{SimpleGraph.Walk.length}\left(p\right)\right)), \exists (j : \operatorname{Fin}\left(\operatorname{SimpleGraph.Walk.length}\left(p\right)\right)), (\operatorname{val}\left(i\right) + 1 < \operatorname{val}\left(j\right)) \land ((\neg ((\operatorname{val}\left(i\right) = 0) \land (\operatorname{val}\left(j\right) + 1 = \operatorname{SimpleGraph.Walk.length}\left(p\right)))) \land (\operatorname{SimpleGraph.Adj}\left(G, \operatorname{SimpleGraph.Walk.getVert}\left(p, \operatorname{val}\left(i\right)\right), \operatorname{SimpleGraph.Walk.getVert}\left(p, \operatorname{val}\left(j\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.HasChord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

A chord joins two nonconsecutive vertices of the closed walk. Positions i and j are in Fin p.length, so the repeated terminal vertex is omitted. The inequality i.val + 1 < j.val orders the positions and excludes successive edges; the additional negation excludes the closing edge from the first to the last position. Walk.getVert takes a natural index: val explicitly displays the coercion from Fin p.length to ℕ.

**Definition 1.5 (Chordal graphs).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), (\operatorname{Chordal}\left(G\right)) \Leftrightarrow (\forall (v : V), \forall (p : \operatorname{SimpleGraph.Walk}\left(G, v, v\right)), (\operatorname{SimpleGraph.Walk.IsCycle}\left(p\right)) \Rightarrow ((4 \le \operatorname{SimpleGraph.Walk.length}\left(p\right)) \Rightarrow (\operatorname{HasChord}\left(p\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.Chordal` (`✓ std3`).

*Citation.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

Definition 4.3, page 7: "A graph is chordal if every induced cycle has length 3." The same source, page 9, says "every cycle of length >3 has a chord." The displayed definition uses the latter literal cycle-and-chord formulation. Cycles are Mathlib SimpleGraph.Walk.IsCycle, and every closed cycle of length at least four must have a chord.

**Definition 1.6 (Faal's existence question).**

$$(claim) \Leftrightarrow (\forall (r : \mathbb{N}), (1 \le r) \Rightarrow (\exists (V : Type), \exists [\operatorname{Fintype}\left(V\right)], \exists [\operatorname{DecidableEq}\left(V\right)], \exists (G : \operatorname{SimpleGraph}\left(V\right)), \exists [\operatorname{DecidableRel}\left(G.Adj\right)], \exists (B : \operatorname{Finset}\left(V\right)), (\operatorname{RConnected}\left(G, r\right)) \land ((\operatorname{SimpleGraph.CliqueFree}\left(G, r + 3\right)) \land ((\neg (\operatorname{Chordal}\left(G\right))) \land (\neg (\operatorname{RealStable}\left(\operatorname{C_{B}}\left(G, B\right)\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.claim` (`✓ std3`).

*Citation.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

Section 7, Open Problems, item 1, page 18: "Necessity of Conditions: Are the conditions of r-connectivity and chordality also necessary? Is there an r-connected K_{r+3}-free non-chordal graph for which C_B(G;x,y) fails to be real-stable?" The claim answers the second sentence for every natural r ≥ 1. V is a finite vertex type, G has decidable adjacency, and B is a Finset of vertices. Clique-freeness is Mathlib SimpleGraph.CliqueFree (r + 3); the final two conjuncts negate chordality and real stability.

**Theorem 1.7 (A family for every positive connectivity).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result` (`✓ std3`). ∎

*Resolves.* `Problems/teimoori-faal-2026-b-restricted-clique-real-stability` (proved) by `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"teimoori-faal-2026-b-restricted-clique-real-stability","declaration_gid":"D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. Teimoori Faal (2026). *A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion*. URL: <https://arxiv.org/abs/2602.24151v1>.

*Commentary.*

Put a = max(r−2,0), take G = K_a ∨ C₄, and mark the cycle vertex of index 0. Cliques of a join split uniquely into cliques of its two factors. The complete factor contributes (1+x)^a and the marked four-cycle contributes (1+2x)(1+x+xy). Thus C_B = (1+x)^a(1+2x)(1+x+xy), which vanishes at x=i and y=−1+i, both with imaginary part 1. After deletion of fewer than r vertices, a remaining complete-graph vertex connects all survivors; if no such vertex remains, at most one cycle vertex was deleted. The induced four-cycle has no chord, and every clique has size at most a+2 < r+3. Natural subtraction r−2 denotes max(r−2,0). For r=1 and r=2 the family is C₄; the assertion is r-connectedness and makes no exact-connectivity claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.C_B`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.Chordal`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.HasChord`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.RConnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.RealStable`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result`
