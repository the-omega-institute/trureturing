# A cubic error-detecting identifying code below density three quarters

## Abstract

A connected cubic graph on fifty vertices has an error-detecting identifying code with thirty-six detectors.

**Definition 1.1 (Closed detector neighborhoods).**

$$\forall (V : Type*), ([\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], \forall (S : \operatorname{Finset}\left(V\right)), (\forall (u : V), (\operatorname{closedDominators}\left(G, S, u\right) = \operatorname{Inter.inter}\left((\operatorname{SimpleGraph.neighborFinset}\left(G, u\right)\cup\left\{u\right\}), S\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.closedDominators` (`✓ std3`).

*Citation.* Devin C. Jean; Suk J. Seo (2022). *Optimal Error-detection system for Identifying Codes*. DOI: [10.48550/arXiv.2208.06052](https://doi.org/10.48550/arXiv.2208.06052). URL: <https://arxiv.org/abs/2208.06052v1>.

*Commentary.*

Page 1, Section 1: "The closed neighborhood of a vertex v ∈ V(G), denoted N[v], is N(v) ∪ {v}." The same paragraph states "N_S[u] = N[u] ∩ S". Here V is the vertex type, G is a finite simple graph, S is its detector set, and u is a vertex. Finset union with the singleton includes u itself; intersection retains exactly the detectors.

**Definition 1.2 (Error-detecting identifying codes).**

$$\forall (V : Type*), ([\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], \forall (S : \operatorname{Finset}\left(V\right)), (\operatorname{IsDETIC}\left(G, S\right) = ((\forall (v : V), (2 \le \operatorname{Finset.card}\left(\operatorname{closedDominators}\left(G, S, v\right)\right))) \land (\forall (u : V), (\forall (v : V), ((u \ne v) \Rightarrow ((2 \le \operatorname{Finset.card}\left((\operatorname{closedDominators}\left(G, S, u\right)\setminus\operatorname{closedDominators}\left(G, S, v\right))\right)) \lor (2 \le \operatorname{Finset.card}\left((\operatorname{closedDominators}\left(G, S, v\right)\setminus\operatorname{closedDominators}\left(G, S, u\right))\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.IsDETIC` (`✓ std3`).

*Citation.* Devin C. Jean; Suk J. Seo (2022). *Optimal Error-detection system for Identifying Codes*. DOI: [10.48550/arXiv.2208.06052](https://doi.org/10.48550/arXiv.2208.06052). URL: <https://arxiv.org/abs/2208.06052v1>.

*Commentary.*

Page 3, Theorem 2.1: "A detector set, S ⊆ V(G), is a DET:IC if and only if each vertex is at least 2-dominated and all pairs are 2#-distinguished." Page 2, Definition 3: "If S is a dominating set and u, v ∈ V(G), u and v are k#-distinguished if |N_S[u] − N_S[v]| ≥ k or |N_S[v] − N_S[u]| ≥ k." The first conjunct requires two closed dominators at every vertex; the second tests both directed differences for each distinct pair, with k=2.

**Definition 1.3 (The cubic density conjecture).**

$$\operatorname{claim} = (\forall (V : Type), ([\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], (\operatorname{SimpleGraph.IsRegularOfDegree}\left(G, 3\right)) \Rightarrow ((\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow (\forall (S : \operatorname{Finset}\left(V\right)), ((\operatorname{IsDETIC}\left(G, S\right)) \Rightarrow (\frac{(3:\mathbb{Q})}{4} \le \frac{(\operatorname{Finset.card}\left(S\right):\mathbb{Q})}{(\operatorname{Fintype.card}\left(V\right):\mathbb{Q})})))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.claim` (`✓ std3`).

*Citation.* Devin C. Jean; Suk J. Seo (2022). *Optimal Error-detection system for Identifying Codes*. DOI: [10.48550/arXiv.2208.06052](https://doi.org/10.48550/arXiv.2208.06052). URL: <https://arxiv.org/abs/2208.06052v1>.

*Commentary.*

Page 9, Section 4.2.2: "Conjecture 1. For a cubic graph G, DET:IC%(G) ≥ 3/4." Page 3 states "Note that density is also defined for finite graphs." The finite assertion says that every error-detecting identifying code has cardinality divided by graph order at least three quarters. Graphs are simple and cubic means degree three at every vertex. Connectedness restricts the domain; a connected counterexample also disproves the assertion without that restriction. All displayed quotients are rational.

**Theorem 1.4 (The conjectured lower bound fails).**

$$\neg (\forall (V : Type), ([\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), ([\operatorname{DecidableRel}\left(\operatorname{G.Adj}\right)], (\operatorname{SimpleGraph.IsRegularOfDegree}\left(G, 3\right)) \Rightarrow ((\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow (\forall (S : \operatorname{Finset}\left(V\right)), ((\operatorname{IsDETIC}\left(G, S\right)) \Rightarrow (\frac{(3:\mathbb{Q})}{4} \le \frac{(\operatorname{Finset.card}\left(S\right):\mathbb{Q})}{(\operatorname{Fintype.card}\left(V\right):\mathbb{Q})})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result` (`✓ std3`). ∎

*Resolves.* `Problems/jean-seo-2022-cubic-error-detecting-identifying-code-density` (refuted) by `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jean-seo-2022-cubic-error-detecting-identifying-code-density","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Devin C. Jean; Suk J. Seo (2022). *Optimal Error-detection system for Identifying Codes*. DOI: [10.48550/arXiv.2208.06052](https://doi.org/10.48550/arXiv.2208.06052). URL: <https://arxiv.org/abs/2208.06052v1>.

*Commentary.*

The vertices 0 through 49 form a connected cubic graph. Vertices 14 through 49 are detectors, giving cardinality 36 and density 36/50=18/25<3/4. The eight A and six B vertices are outside the code; the twelve vertices of each of the P, Q and R types belong to it. Their closed detector neighborhoods have sizes 3, 2, 2, 4 and 3 respectively. Explicit finite neighborhood tables verify two-domination and directed separation, and a spanning tree verifies connectedness. This finite counterexample disproves the lower bound; it asserts neither minimality of this code nor optimality of 18/25 over cubic graphs. The source's examples at densities 3/4 and 7/8 remain compatible with this counterexample.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.IsDETIC`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.closedDominators`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result`
