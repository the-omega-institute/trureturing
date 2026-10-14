# ColorSym need not find an existing list multicoloring

## Abstract

A colorable K4 list assignment defeats every ColorSym execution.

**Definition 1.1 (Color support).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall c \in \mathbb{Z},\; \operatorname{supp}\left(L, c\right) = \operatorname{Finset}.\operatorname{filter}\left(\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto c \in L\left(i\right), \operatorname{Finset}.\operatorname{univ}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.supp` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

The support of an integer color is the set of vertices whose lists contain it. Vertices of the complete graph are indexed by Fin n, with the paper's indices shifted down by one.

**Definition 1.2 (Proper intersections).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Ip}\left(L, S\right) = \operatorname{Finset}.\operatorname{filter}\left(\operatorname{fun} (c : \mathbb{Z}) \mapsto \operatorname{supp}\left(L, c\right) = S, \operatorname{Finset}.\operatorname{biUnion}\left(\operatorname{Finset}.\operatorname{univ}, L\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.Ip` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 2.1, p. 59, defines the proper intersection by taking the intersection of the selected lists and removing the union of all other lists. Here colors are integers in the union of the lists, filtered by exact support; the empty support has empty proper intersection.

**Definition 1.3 (List multicoloring).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall b \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \operatorname{IsColoring}\left(L, b, p\right) = \left((\forall i \in \operatorname{Fin}\left(n\right),\; (p\left(i\right) \subseteq L\left(i\right)) \land (\operatorname{Finset}.\operatorname{card}\left(p\left(i\right)\right) = b)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (i \ne j) \Rightarrow (\operatorname{Disjoint}\left(p\left(i\right), p\left(j\right)\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.IsColoring` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 1, pp. 57–58: "a coloring function φ on the vertices of G that assigns to each vertex v a subset of b elements from L(v) in such a way that φ(u) ∩ φ(v) = ∅ for any uv ∈ E(G)". For a complete graph, every pair of distinct vertices is adjacent. The symbol p denotes φ.

**Definition 1.4 (Existence of a list multicoloring).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall b \in \mathbb{N},\; \operatorname{Colorable}\left(L, b\right) = \left(\exists p \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \operatorname{IsColoring}\left(L, b, p\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.Colorable` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

A list assignment is colorable when such a family of disjoint b-element subsets exists.

**Definition 1.5 (Order of supports).**

$$\forall n \in \mathbb{N},\; \forall ord \in \operatorname{List}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{AdmissibleOrder}\left(ord\right) = \left((\operatorname{List}.\operatorname{Nodup}\left(ord\right)) \land \left((\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (S \in ord) \Leftrightarrow (2 \le \operatorname{Finset}.\operatorname{card}\left(S\right))) \land (\operatorname{List}.\operatorname{Pairwise}\left(\operatorname{fun} (S : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{fun} (T : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left(S\right) \le \operatorname{Finset}.\operatorname{card}\left(T\right), ord\right))\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.AdmissibleOrder` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "Otherwise, for each set S with |S| = i, consider |Ip(S)|". The order contains every support of size at least two exactly once, with nondecreasing size.

**Definition 1.6 (Choosing a color).**

$$\forall pick \in \operatorname{Finset}\left(\mathbb{Z}\right) \to \mathbb{Z},\; \operatorname{AdmissiblePick}\left(pick\right) = \left(\forall s \in \operatorname{Finset}\left(\mathbb{Z}\right),\; (\operatorname{Finset}.\operatorname{Nonempty}\left(s\right)) \Rightarrow (pick\left(s\right) \in s)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.AdmissiblePick` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "Remove a color from Ip(S) and assign it to vj." The function pick selects an element from every nonempty integer-color pool.

**Definition 1.7 (Least-loaded vertex and tie breaking).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; ((\operatorname{Finset}.\operatorname{sort}\left(\operatorname{Finset}.\operatorname{filter}\left(\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \forall j \in \operatorname{Fin}\left(n\right),\; (j \in S) \Rightarrow (w\left(i\right) \le w\left(j\right)), S\right), \operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto i \le j\right) = []) \Rightarrow (\operatorname{best}\left(S, w\right) = \operatorname{none})) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \forall rest \in \operatorname{List}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{Finset}.\operatorname{sort}\left(\operatorname{Finset}.\operatorname{filter}\left(\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \forall j \in \operatorname{Fin}\left(n\right),\; (j \in S) \Rightarrow (w\left(i\right) \le w\left(j\right)), S\right), \operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto i \le j\right) = \operatorname{List}.\operatorname{cons}\left(j, rest\right)) \Rightarrow (\operatorname{best}\left(S, w\right) = \operatorname{some}\left(j\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.best` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "let j ∈ S be the index for which w(j) is minimum (if more than one j with minimum w, then take the smallest index)". Sorting the set of minimizers in ascending vertex order selects exactly this vertex.

**Definition 1.8 (Stopping condition).**

$$\forall n \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall st \in (\operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right)) \times (\operatorname{Fin}\left(n\right) \to \mathbb{N}),\; \operatorname{stopped}\left(b, st\right) = \operatorname{decide}\left(\forall j \in \operatorname{Fin}\left(n\right),\; b \le (st).2\left(j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.stopped` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "If wi ≥ b for each i or i = n + 1, then Stop." The first component of st records output sets and the second records their loads. Exhausting the support list implements the terminal step n + 1.

**Definition 1.9 (Assigning one color).**

$$\forall n \in \mathbb{N},\; \forall st \in (\operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right)) \times (\operatorname{Fin}\left(n\right) \to \mathbb{N}),\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall c \in \mathbb{Z},\; \operatorname{assign}\left(st, j, c\right) = \langle\operatorname{Function}.\operatorname{update}\left((st).1, j, \operatorname{insert}\left(c, (st).1\left(j\right)\right)\right), \operatorname{Function}.\operatorname{update}\left((st).2, j, (st).2\left(j\right) + 1\right)\rangle$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.assign` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

A color is inserted at the selected vertex and its load increases by one.

**Definition 1.10 (Processing one proper intersection).**

$$\forall n \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall b \in \mathbb{N},\; \forall pick \in \operatorname{Finset}\left(\mathbb{Z}\right) \to \mathbb{Z},\; \forall pool \in \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall st \in (\operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right)) \times (\operatorname{Fin}\left(n\right) \to \mathbb{N}),\; (\operatorname{runPool}\left(S, b, pick, 0, pool, st\right) = st) \land (\forall fuel \in \mathbb{N},\; \operatorname{runPool}\left(S, b, pick, fuel + 1, pool, st\right) = \operatorname{if} \operatorname{stopped}\left(b, st\right) \operatorname{then} st \operatorname{else} \operatorname{if} pool = \emptyset \operatorname{then} st \operatorname{else} \operatorname{match} \operatorname{best}\left(S, (st).2\right) \operatorname{with} | \operatorname{none} \mapsto st | \operatorname{some}\left(j\right) \mapsto \operatorname{let} c := pick\left(pool\right); \operatorname{runPool}\left(S, b, pick, fuel, \operatorname{Finset}.\operatorname{erase}\left(pool, c\right), \operatorname{assign}\left(st, j, c\right)\right))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.runPool` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "Goto Step i until Ip(S) is empty." The fuel is initially the pool cardinality. Each assignment erases the chosen color, so an admissible pick decreases that cardinality by one.

**Definition 1.11 (Processing all supports).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall b \in \mathbb{N},\; \forall pick \in \operatorname{Finset}\left(\mathbb{Z}\right) \to \mathbb{Z},\; \forall st \in (\operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right)) \times (\operatorname{Fin}\left(n\right) \to \mathbb{N}),\; (\operatorname{runSupports}\left(L, b, pick, [], st\right) = st) \land (\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall ord \in \operatorname{List}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{runSupports}\left(L, b, pick, \operatorname{List}.\operatorname{cons}\left(S, ord\right), st\right) = \operatorname{runSupports}\left(L, b, pick, ord, \operatorname{runPool}\left(S, b, pick, \operatorname{Finset}.\operatorname{card}\left(\operatorname{Ip}\left(L, S\right)\right), \operatorname{Ip}\left(L, S\right), st\right)\right))$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.runSupports` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Each support is processed with its proper intersection as the color pool. The empty list returns the current pair of outputs and loads.

**Definition 1.12 (Singleton proper intersections).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \operatorname{initial}\left(L\right) = \langle\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Ip}\left(L, \{i\}\right), \operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Finset}.\operatorname{card}\left(\operatorname{Ip}\left(L, \{i\}\right)\right)\rangle$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.initial` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "Color every proper intersections of sets of size 1: vi gets |Ip({i})| colors. Thus wi = |Ip({i})|." All singleton proper intersections are assigned before shared colors are processed.

**Definition 1.13 (ColorSym output).**

$$\forall n \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall b \in \mathbb{N},\; \forall ord \in \operatorname{List}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall pick \in \operatorname{Finset}\left(\mathbb{Z}\right) \to \mathbb{Z},\; \operatorname{colorSym}\left(L, b, ord, pick\right) = (\operatorname{runSupports}\left(L, b, pick, ord, \operatorname{initial}\left(L\right)\right)).1$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.colorSym` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

The output is the first component of the final pair after the singleton step and all ordered supports.

**Definition 1.14 (ColorSym optimality conjecture).**

$$claim = \left(\forall n \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall L \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Finset}.\operatorname{card}\left(L\left(i\right)\right) = a) \Rightarrow ((\operatorname{Colorable}\left(L, b\right)) \Rightarrow (\exists ord \in \operatorname{List}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \exists pick \in \operatorname{Finset}\left(\mathbb{Z}\right) \to \mathbb{Z},\; (\operatorname{AdmissibleOrder}\left(ord\right)) \land \left((\operatorname{AdmissiblePick}\left(pick\right)) \land (\exists p \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\mathbb{Z}\right),\; (\operatorname{IsColoring}\left(L, b, p\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; p\left(i\right) \subseteq \operatorname{colorSym}\left(L, b, ord, pick\right)\left(i\right)))\right)))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.claim` (`✓ std3`).

*Citation.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Section 3.1, p. 63: "We conjecture that this algorithm is optimal (i.e., produces an (L, b)-coloring if K_n is (L, b)-colorable)." The parameters n, a and b are natural numbers, L assigns finite integer-color lists, and every list has exactly a elements. The formula allows any admissible support order and color selection, and asks only for a b-coloring contained in the output.

**Theorem 1.15 (The optimality conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/godin-grisot-togni-2022-colorsym-optimality` (refuted) by `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"godin-grisot-togni-2022-colorsym-optimality","declaration_gid":"D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean-Christophe Godin; Rémi Grisot; Olivier Togni (2025). *On List Coloring with Separation of the Complete Graph and Set System Intersections*. DOI: [10.5614/ejgta.2025.13.1.5](https://doi.org/10.5614/ejgta.2025.13.1.5). URL: <https://arxiv.org/abs/2209.03436>.

*Commentary.*

Take four lists {1,2,3,4,5,6}, {1,2,3,4,7,8}, {5,6,9,10,11,12}, and {5,6,13,14,15,16}, and b = 4. The disjoint subsets {1,2,5,6}, {3,4,7,8}, {9,10,11,12}, and {13,14,15,16} form a 4-coloring. Every ColorSym execution has final loads (5,3,4,4), independently of color choice. Vertex 2 receives only three colors. Current-load balancing spends the pair pool on vertex 1 before its later triple pool, while vertex 2 has no later supply.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.AdmissibleOrder`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.AdmissiblePick`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.Colorable`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.Ip`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.IsColoring`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.assign`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.best`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.claim`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.colorSym`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.initial`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.result`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.runPool`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.runSupports`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.stopped`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.supp`
