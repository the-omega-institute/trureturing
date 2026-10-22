# The Luiz–Vieira generalized Blanuša closing conjecture is false

## Abstract

The first generalized Blanuša snark has a [21]-Roman function of weight 108 and every independent [21]-Roman function has weight at least 110.

**Definition 1.1 (Active neighbours).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall f \in V \to \mathbb{N},\; \forall v \in V,\; \operatorname{activeNbrs}\left(G, f, v\right) = \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} (u : V) \mapsto 0 < f\left(u\right)), \operatorname{SimpleGraph}.\operatorname{neighborFinset}\left(G, v\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.activeNbrs` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 1: "the active neighborhood of v under f, denoted by AN(v), is the set of vertices w ∈ N(v) such that f(w) ≥ 1." The filter is over the open neighbour finset.

**Definition 1.2 ([k]-Roman dominating functions).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall k \in \mathbb{N},\; \forall f \in V \to \mathbb{N},\; (\operatorname{IsRomanDom}\left(G, k, f\right)) \Leftrightarrow ((\forall v \in V,\; f\left(v\right) \le k + 1) \land (\forall v \in V,\; (f\left(v\right) < k) \Rightarrow (k + \operatorname{Finset}.\operatorname{card}\left(\operatorname{activeNbrs}\left(G, f, v\right)\right) \le f\left(v\right) + \operatorname{Finset}.\operatorname{sum}\left(\operatorname{SimpleGraph}.\operatorname{neighborFinset}\left(G, v\right), f\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.IsRomanDom` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 1: "For any integer k ≥ 1, a [k]-Roman dominating function on G, also called [k]-RDF, is a function f : V(G) → {0, 1, . . . , k + 1} such that f(N[v]) ≥ k + |AN(v)| for every vertex v ∈ V(G) with f(v) < k." The displayed natural-valued encoding gives the same finite label interval.

**Definition 1.3 (Independent [k]-Roman dominating functions).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall k \in \mathbb{N},\; \forall f \in V \to \mathbb{N},\; (\operatorname{IsIndepRomanDom}\left(G, k, f\right)) \Leftrightarrow ((\operatorname{IsRomanDom}\left(G, k, f\right)) \land (\forall u \in V,\; \forall w \in V,\; (0 < f\left(u\right)) \Rightarrow ((0 < f\left(w\right)) \Rightarrow (\neg \operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\left(u, w\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.IsIndepRomanDom` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 1: "A [k]-Roman dominating function f = (V0, V1, . . . , Vk+1) on a graph G is called an independent [k]-Roman dominating function, or [k]-IRDF for short, if the set of active vertices V1 ∪ V2 ∪ · · · ∪ Vk+1 is an independent set." Positive labels encode the active set.

**Definition 1.4 (Roman weight).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall f \in V \to \mathbb{N},\; \operatorname{weight}\left(f\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, f\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.weight` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 1: "The weight of a [k]-RDF f on G is defined as ω(f) = f(V(G)) = Σ_{v∈V(G)} f(v)."

**Definition 1.5 ([k]-Roman domination number).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall k \in \mathbb{N},\; \operatorname{gammaRoman}\left(G, k\right) = \operatorname{sInf}\left(\{w : \mathbb{N} \mid \exists f \in V \to \mathbb{N},\; (\operatorname{IsRomanDom}\left(G, k, f\right)) \land (\operatorname{weight}\left(f\right) = w)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.gammaRoman` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 1: "The [k]-Roman domination number of G is the minimum weight that a [k]-RDF of G can have, and is denoted by γ[kR](G)."

**Definition 1.6 (Independent [k]-Roman domination number).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall k \in \mathbb{N},\; \operatorname{indepRoman}\left(G, k\right) = \operatorname{sInf}\left(\{w : \mathbb{N} \mid \exists f \in V \to \mathbb{N},\; (\operatorname{IsIndepRomanDom}\left(G, k, f\right)) \land (\operatorname{weight}\left(f\right) = w)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.indepRoman` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 1: "The independent [k]-Roman domination number i[kR](G) is the minimum weight of an independent [k]-IRDF on G".

**Definition 1.7 (Blanuša vertex labels).**

$$\begin{aligned}\operatorname{Vert}.\operatorname{blk} : \operatorname{Fin}\left(10\right) \to \operatorname{Vert}\left(\right)\\\operatorname{Vert}.\operatorname{lnk} : \mathbb{N} \to \left(\operatorname{Fin}\left(8\right) \to \operatorname{Vert}\left(\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.Vert` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

The inductive type has exactly the two displayed constructors. Figure 5 labels the ten vertices of B₀ᵗ by blk 0 through blk 9 and the eight vertices of each link Lⱼ by lnk j 0 through lnk j 7.

**Definition 1.8 (Block border vertex a).**

$$\operatorname{a}\left(\right) = \operatorname{Vert}.\operatorname{blk}\left(0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.a` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(a) names a = blk 0.

**Definition 1.9 (Block border vertex b).**

$$\operatorname{b}\left(\right) = \operatorname{Vert}.\operatorname{blk}\left(6\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.b` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(a) names b = blk 6.

**Definition 1.10 (Block border vertex c).**

$$\operatorname{c}\left(\right) = \operatorname{Vert}.\operatorname{blk}\left(3\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.c` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(a) names c = blk 3.

**Definition 1.11 (Block border vertex d).**

$$\operatorname{d}\left(\right) = \operatorname{Vert}.\operatorname{blk}\left(9\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.d` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(a) names d = blk 9.

**Definition 1.12 (Link border vertex x).**

$$\forall j \in \mathbb{N},\; \operatorname{x}\left(j\right) = \operatorname{Vert}.\operatorname{lnk}\left(j, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.x` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(c) names xⱼ = lnk j 0.

**Definition 1.13 (Link border vertex w).**

$$\forall j \in \mathbb{N},\; \operatorname{w}\left(j\right) = \operatorname{Vert}.\operatorname{lnk}\left(j, 2\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.w` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(c) names wⱼ = lnk j 2.

**Definition 1.14 (Link border vertex y).**

$$\forall j \in \mathbb{N},\; \operatorname{y}\left(j\right) = \operatorname{Vert}.\operatorname{lnk}\left(j, 5\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.y` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(c) names yⱼ = lnk j 5.

**Definition 1.15 (Link border vertex z).**

$$\forall j \in \mathbb{N},\; \operatorname{z}\left(j\right) = \operatorname{Vert}.\operatorname{lnk}\left(j, 7\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.z` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(c) names zⱼ = lnk j 7.

**Definition 1.16 (Edges of B₀¹).**

$$\operatorname{blockOneEdges}\left(\right) = \left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(0\right), \operatorname{Vert}.\operatorname{blk}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(1\right), \operatorname{Vert}.\operatorname{blk}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(2\right), \operatorname{Vert}.\operatorname{blk}\left(3\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(3\right), \operatorname{Vert}.\operatorname{blk}\left(9\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(9\right), \operatorname{Vert}.\operatorname{blk}\left(8\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(8\right), \operatorname{Vert}.\operatorname{blk}\left(7\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(7\right), \operatorname{Vert}.\operatorname{blk}\left(6\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(6\right), \operatorname{Vert}.\operatorname{blk}\left(4\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(4\right), \operatorname{Vert}.\operatorname{blk}\left(0\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(1\right), \operatorname{Vert}.\operatorname{blk}\left(7\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(2\right), \operatorname{Vert}.\operatorname{blk}\left(5\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(5\right), \operatorname{Vert}.\operatorname{blk}\left(8\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(4\right), \operatorname{Vert}.\operatorname{blk}\left(5\right)\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.blockOneEdges` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(a) gives the thirteen unordered edges of B₀¹.

**Definition 1.17 (Edges of B₀²).**

$$\operatorname{blockTwoEdges}\left(\right) = \left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(0\right), \operatorname{Vert}.\operatorname{blk}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(1\right), \operatorname{Vert}.\operatorname{blk}\left(3\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(1\right), \operatorname{Vert}.\operatorname{blk}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(2\right), \operatorname{Vert}.\operatorname{blk}\left(8\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(2\right), \operatorname{Vert}.\operatorname{blk}\left(5\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(0\right), \operatorname{Vert}.\operatorname{blk}\left(4\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(4\right), \operatorname{Vert}.\operatorname{blk}\left(6\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(4\right), \operatorname{Vert}.\operatorname{blk}\left(5\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(5\right), \operatorname{Vert}.\operatorname{blk}\left(7\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(3\right), \operatorname{Vert}.\operatorname{blk}\left(7\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(7\right), \operatorname{Vert}.\operatorname{blk}\left(9\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(6\right), \operatorname{Vert}.\operatorname{blk}\left(8\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{blk}\left(8\right), \operatorname{Vert}.\operatorname{blk}\left(9\right)\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.blockTwoEdges` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(b) gives the thirteen unordered edges of B₀².

**Definition 1.18 (Edges of Lⱼ).**

$$\forall j \in \mathbb{N},\; \operatorname{linkEdges}\left(j\right) = \left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 0\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 1\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 2\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 4\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 4\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 7\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 7\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 6\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 6\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 5\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 5\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 3\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 3\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 0\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 1\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 6\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Vert}.\operatorname{lnk}\left(j, 3\right), \operatorname{Vert}.\operatorname{lnk}\left(j, 4\right)\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.linkEdges` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Figure 5(c) gives the ten edges of each link block Lⱼ.

**Definition 1.19 (Base block edge selector).**

$$\forall t \in \mathbb{N},\; \operatorname{blockEdges}\left(t\right) = \operatorname{ite}\left(t = 1, \operatorname{blockOneEdges}\left(\right), \operatorname{blockTwoEdges}\left(\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.blockEdges` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

The base block is B₀¹ when t = 1 and B₀² otherwise.

**Definition 1.20 (Vertices of Lⱼ).**

$$\forall j \in \mathbb{N},\; \operatorname{linkVerts}\left(j\right) = \operatorname{Finset}.\operatorname{image}\left((\operatorname{fun} (r : \operatorname{Fin}\left(8\right)) \mapsto \operatorname{Vert}.\operatorname{lnk}\left(j, r\right)), \operatorname{Finset}.\operatorname{univ}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.linkVerts` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Each Lⱼ has the eight vertices lnk j r for r ∈ Fin 8.

**Definition 1.21 (Edges of the link graph).**

$$\forall i \in \mathbb{N},\; \operatorname{linkGraphEdges}\left(i\right) = ((\operatorname{linkEdges}\left(i - 1\right)) \cup (\operatorname{linkEdges}\left(i\right))) \cup (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{w}\left(i - 1\right), \operatorname{y}\left(i\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{z}\left(i - 1\right), \operatorname{x}\left(i\right)\right)\right\})$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.linkGraphEdges` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 4, Figure 8: E(LGᵢ) = E(Lᵢ₋₁) ∪ E(Lᵢ) ∪ {wᵢ₋₁yᵢ, zᵢ₋₁xᵢ}.

**Definition 1.22 (Vertices of Bᵢᵗ).**

$$\begin{aligned}\operatorname{verts}\left(0\right) = \operatorname{Finset}.\operatorname{image}\left(\operatorname{Vert}.\operatorname{blk}, \operatorname{Finset}.\operatorname{univ}\right)\\\operatorname{verts}\left(1\right) = (\operatorname{Finset}.\operatorname{image}\left(\operatorname{Vert}.\operatorname{blk}, \operatorname{Finset}.\operatorname{univ}\right)) \cup (\operatorname{linkVerts}\left(1\right))\\\operatorname{verts}\left(2\right) = ((\operatorname{Finset}.\operatorname{image}\left(\operatorname{Vert}.\operatorname{blk}, \operatorname{Finset}.\operatorname{univ}\right)) \cup (\operatorname{linkVerts}\left(1\right))) \cup (\operatorname{linkVerts}\left(2\right))\\\forall i \in \mathbb{N},\; \operatorname{verts}\left(i + 3\right) = (\operatorname{verts}\left(i + 1\right)) \cup ((\operatorname{linkVerts}\left(i + 2\right)) \cup (\operatorname{linkVerts}\left(i + 3\right)))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.verts` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 4: V(Bᵢᵗ) is the base block together with the required link blocks, recursively adding two links at each step.

**Definition 1.23 (Edges of Bᵢᵗ).**

$$\forall t \in \mathbb{N},\; \begin{aligned}\operatorname{edges}\left(t, 0\right) = \operatorname{blockEdges}\left(t\right)\\\operatorname{edges}\left(t, 1\right) = \operatorname{ite}\left(t = 1, ((\operatorname{blockEdges}\left(t\right)) \cup (\operatorname{linkEdges}\left(1\right))) \cup (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{c}\left(\right), \operatorname{y}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{d}\left(\right), \operatorname{x}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{a}\left(\right), \operatorname{z}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{b}\left(\right), \operatorname{w}\left(1\right)\right)\right\}), ((\operatorname{blockEdges}\left(t\right)) \cup (\operatorname{linkEdges}\left(1\right))) \cup (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{b}\left(\right), \operatorname{w}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{a}\left(\right), \operatorname{z}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{c}\left(\right), \operatorname{y}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{d}\left(\right), \operatorname{x}\left(1\right)\right)\right\})\right)\\\operatorname{edges}\left(t, 2\right) = \operatorname{ite}\left(t = 1, (((\operatorname{blockEdges}\left(t\right)) \cup (\operatorname{linkEdges}\left(1\right))) \cup (\operatorname{linkEdges}\left(2\right))) \cup (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{c}\left(\right), \operatorname{y}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{d}\left(\right), \operatorname{x}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{w}\left(1\right), \operatorname{y}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{z}\left(1\right), \operatorname{x}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{a}\left(\right), \operatorname{z}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{b}\left(\right), \operatorname{w}\left(2\right)\right)\right\}), (((\operatorname{blockEdges}\left(t\right)) \cup (\operatorname{linkEdges}\left(1\right))) \cup (\operatorname{linkEdges}\left(2\right))) \cup (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{b}\left(\right), \operatorname{w}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{a}\left(\right), \operatorname{z}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{c}\left(\right), \operatorname{y}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{d}\left(\right), \operatorname{x}\left(1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{z}\left(1\right), \operatorname{x}\left(2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{w}\left(1\right), \operatorname{y}\left(2\right)\right)\right\})\right)\\\forall i \in \mathbb{N},\; \operatorname{edges}\left(t, i + 3\right) = (((\operatorname{edges}\left(t, i + 1\right)) \setminus (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{a}\left(\right), \operatorname{z}\left(i + 1\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{b}\left(\right), \operatorname{w}\left(i + 1\right)\right)\right\})) \cup (\operatorname{linkGraphEdges}\left(i + 3\right))) \cup (\left\{\operatorname{Sym2}.\operatorname{mk}\left(\operatorname{w}\left(i + 1\right), \operatorname{y}\left(i + 2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{z}\left(i + 1\right), \operatorname{x}\left(i + 2\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{a}\left(\right), \operatorname{z}\left(i + 3\right)\right), \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{b}\left(\right), \operatorname{w}\left(i + 3\right)\right)\right\})\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.edges` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 4: "For each integer i, with i ≥ 3, the snark Bᵢᵗ is obtained recursively from the snark Bᵗᵢ₋₂ and the link graph LGᵢ" with the displayed edge deletion and insertion sets.

**Definition 1.24 (Generalized Blanuša snark).**

$$\forall t \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{snark}\left(t, i\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left((\operatorname{fun} (u : \operatorname{Subtype}\left((\operatorname{fun} (q : \operatorname{Vert}\left(\right)) \mapsto q \in \operatorname{verts}\left(i\right))\right)) \mapsto (\operatorname{fun} (v : \operatorname{Subtype}\left((\operatorname{fun} (q : \operatorname{Vert}\left(\right)) \mapsto q \in \operatorname{verts}\left(i\right))\right)) \mapsto \operatorname{Sym2}.\operatorname{mk}\left(\operatorname{Subtype}.\operatorname{val}\left(u\right), \operatorname{Subtype}.\operatorname{val}\left(v\right)\right) \in \operatorname{edges}\left(t, i\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.snark` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

The graph Bᵢᵗ is the SimpleGraph.fromRel graph on the vertex subtype v ∈ verts i, with adjacency represented by Sym2.mk membership in edges t i.

**Definition 1.25 (The closing conjecture).**

$$(claim) \Leftrightarrow (\forall t \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall k \in \mathbb{N},\; ((t = 1) \lor (t = 2)) \Rightarrow ((1 \le i) \Rightarrow ((2 \le k) \Rightarrow (\operatorname{gammaRoman}\left(\operatorname{snark}\left(t, i\right), k\right) = \operatorname{indepRoman}\left(\operatorname{snark}\left(t, i\right), k\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.claim` (`✓ std3`).

*Citation.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

Section 6: "another interesting line of research is finding other classes of graphs with ∆(G) ≤ 3 for which γ[kR](G) = i[kR](G) for k ≥ 2. In fact, we conjecture that this property holds for all generalized Blanuša snarks." The parameters are encoded by t ∈ {1, 2}, i ≥ 1 and k ≥ 2.

**Theorem 1.26 (A counterexample at B₁¹ and k = 21).**

$$\neg \left(\forall t \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall k \in \mathbb{N},\; ((t = 1) \lor (t = 2)) \Rightarrow ((1 \le i) \Rightarrow ((2 \le k) \Rightarrow (\operatorname{gammaRoman}\left(\operatorname{snark}\left(t, i\right), k\right) = \operatorname{indepRoman}\left(\operatorname{snark}\left(t, i\right), k\right))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. G. Luiz and F. A. S. Vieira (2025). *Independent [k]-Roman Domination on Graphs*. DOI: [10.7151/dmgt.2580](https://doi.org/10.7151/dmgt.2580). URL: <https://arxiv.org/abs/2406.11688v1>.

*Commentary.*

For B₁¹, the constant label 6 is a [21]-RDF of weight 108, while the independent witness has five positive labels of 22 and hence weight 110. Thus γ[21R](B₁¹) ≤ 108 < 110 = i[21R](B₁¹), refuting the closing conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.IsIndepRomanDom`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.IsRomanDom`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.Vert`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.a`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.activeNbrs`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.b`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.blockEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.blockOneEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.blockTwoEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.c`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.d`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.gammaRoman`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.indepRoman`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.linkEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.linkGraphEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.linkVerts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.snark`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.verts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.w`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.x`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.y`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.z`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting](../DominatingSetAverageBoundCounting.md)
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem](../DominatingSetAverageBoundNonstem.md)
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](../../../ConceptDynamics/GraphColoring/GraphCoverDomination.md)
