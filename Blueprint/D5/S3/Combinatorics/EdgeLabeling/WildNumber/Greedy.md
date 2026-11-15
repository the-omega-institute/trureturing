# Greedy

## Abstract

Finite edge-colored graphs and their greedy color-connecting sets.

**Definition 1.1 (colorEdges).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{c} : \operatorname{C}) , \operatorname{colorEdges} \operatorname{G} \gamma \operatorname{c} = \{ \operatorname{e} : \operatorname{Sym2} \operatorname{V} | \exists \operatorname{h} : \operatorname{e} \in \operatorname{G} . \operatorname{edgeSet} , \gamma \langle \operatorname{e} , \operatorname{h} \rangle = \operatorname{c} \}$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.colorEdges` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 1: “For any color cᵢ ∈ C, let Eᵢ(G) = {e ∈ E(G) : γ(e) = cᵢ}, and let Gᵢ be the graph with vertex set V(G) and edge set Eᵢ(G).” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Definition 1.2 (wildColorGraph).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) (\operatorname{c} : \operatorname{C}) , \operatorname{wildColorGraph} \operatorname{G} \gamma \operatorname{W} \operatorname{c} = \operatorname{SimpleGraph} . \operatorname{fromEdgeSet} ((\operatorname{W} : \operatorname{Set} (\operatorname{Sym2} \operatorname{V})) \cup \operatorname{colorEdges} \operatorname{G} \gamma \operatorname{c})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.wildColorGraph` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 2: “For any color cᵢ, define the graph Gᵢᵂ to be the subgraph of G with vertex set V(G) and edge set W ∪ Eᵢ(G).” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Definition 1.3 (IsColorConnecting).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) , \operatorname{IsColorConnecting} \operatorname{G} \gamma \operatorname{W} \iff ((\operatorname{W} : \operatorname{Set} (\operatorname{Sym2} \operatorname{V})) \subseteq \operatorname{G} . \operatorname{edgeSet} \land (\forall \operatorname{c} , (\operatorname{wildColorGraph} \operatorname{G} \gamma \operatorname{W} \operatorname{c}) . \operatorname{Connected}))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsColorConnecting` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 2: “If the set of edges W is such that for every cᵢ ∈ C, the subgraph Gᵢᵂ is connected, then W is a color-connecting set.” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Definition 1.4 (wildNumber).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) , \operatorname{wildNumber} \operatorname{G} \gamma = \operatorname{sInf} \{ \operatorname{k} : \mathbb{N} | \exists \operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V}) , \operatorname{IsColorConnecting} \operatorname{G} \gamma \operatorname{W} \land \operatorname{W} . \operatorname{card} = \operatorname{k} \}$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.wildNumber` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 2: “A color-connecting set of minimal size is an ideal wild set. The wild number of G, denoted wld(G), is the size of an ideal wild set of G.” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Definition 1.5 (dip).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) (\operatorname{e} : \operatorname{Sym2} \operatorname{V}) , \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{e} = \sum \operatorname{c} : \operatorname{C} , (\operatorname{Nat} . \operatorname{card} (\operatorname{wildColorGraph} \operatorname{G} \gamma \operatorname{W} \operatorname{c}) . \operatorname{ConnectedComponent} - \operatorname{Nat} . \operatorname{card} (\operatorname{wildColorGraph} \operatorname{G} \gamma (\operatorname{insert} \operatorname{e} \operatorname{W}) \operatorname{c}) . \operatorname{ConnectedComponent})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.dip` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 2: “The dip number of an edge e is δ(e) = #{i : edge e helps color cᵢ} = ∑ᵢ (κ(Gᵢ) − κ(Gᵢᵉ)), which tells us how many colors we can help by coloring that edge wild.” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Definition 1.6 (potential).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) (\operatorname{e} : \operatorname{Sym2} \operatorname{V}) , \operatorname{potential} \operatorname{G} \gamma \operatorname{W} \operatorname{e} = (((\operatorname{Set} . \operatorname{toFinite} \operatorname{G} . \operatorname{edgeSet}) . \operatorname{toFinset}) . \operatorname{val} . \operatorname{map} (\operatorname{dip} \operatorname{G} \gamma (\operatorname{insert} \operatorname{e} \operatorname{W}))) . \operatorname{sort} (\cdot \geq \cdot)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.potential` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 15: “The potential of an edge e in an edge-colored graph G is the nonincreasing dip sequence of the graph G/e.” Section 5.2, PDF page 15: “The potential of an edge e in an edge-colored graph G is the nonincreasing dip sequence of the graph G/e.” Example 5.9 includes the contracted edge with dip 0. Nat.card counts connected components, and natural subtraction is truncated at zero.

**Definition 1.7 (IsGreedyStep).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) (\operatorname{e} : \operatorname{Sym2} \operatorname{V}) , \operatorname{IsGreedyStep} \operatorname{G} \gamma \operatorname{W} \operatorname{e} \iff (\neg \operatorname{IsColorConnecting} \operatorname{G} \gamma \operatorname{W} \land \operatorname{e} \in (\operatorname{Set} . \operatorname{toFinite} \operatorname{G} . \operatorname{edgeSet}) . \operatorname{toFinset} \setminus \operatorname{W} \land (\forall \operatorname{f} \in (\operatorname{Set} . \operatorname{toFinite} \operatorname{G} . \operatorname{edgeSet}) . \operatorname{toFinset} \setminus \operatorname{W} , \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{f} \leq \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{e}) \land (\forall \operatorname{f} \in (\operatorname{Set} . \operatorname{toFinite} \operatorname{G} . \operatorname{edgeSet}) . \operatorname{toFinset} \setminus \operatorname{W} , \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{f} = \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{e} \to \neg \operatorname{List} . \operatorname{Lex} (\cdot < \cdot) (\operatorname{potential} \operatorname{G} \gamma \operatorname{W} \operatorname{e}) (\operatorname{potential} \operatorname{G} \gamma \operatorname{W} \operatorname{f})))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsGreedyStep` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 15: “Order the edges in G/W with the highest dip number lexicographically by potential in G/W (i.e., compare first terms of potential, highest wins; if tie, compare next term; etc.).” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Definition 1.8 (IsGreedyRun).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] , \operatorname{inductive} \operatorname{IsGreedyRun} (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V}) \to \operatorname{Prop} | \operatorname{IsGreedyRun} . \operatorname{empty} : \operatorname{IsGreedyRun} \operatorname{G} \gamma \emptyset | \operatorname{IsGreedyRun} . \operatorname{step} : \forall (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) (\operatorname{e} : \operatorname{Sym2} \operatorname{V}) , \operatorname{IsGreedyRun} \operatorname{G} \gamma \operatorname{W} \to \operatorname{IsGreedyStep} \operatorname{G} \gamma \operatorname{W} \operatorname{e} \to \operatorname{IsGreedyRun} \operatorname{G} \gamma (\operatorname{insert} \operatorname{e} \operatorname{W})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsGreedyRun` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 15: “Initialize by letting W = ∅. While the graph G/W is not color-connected, do the following two steps:” IsGreedyRun is the least predicate inductively generated by the two displayed constructors. Each step inserts one edge maximizing dip and then potential.

**Definition 1.9 (IsGreedyOutput).**

$$\forall (\operatorname{V} \operatorname{C} : \operatorname{Type}) [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) , \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{W} \iff (\operatorname{IsGreedyRun} \operatorname{G} \gamma \operatorname{W} \land \operatorname{IsColorConnecting} \operatorname{G} \gamma \operatorname{W})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsGreedyOutput` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

PDF page 15: “When G/W is color-connected, return the set W.” The vertices form V and the color set is C. Natural subtraction is truncated at zero.

**Theorem 1.10 (kappa connected).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} , \operatorname{G} . \operatorname{Connected} \to \operatorname{Nat} . \operatorname{card} \operatorname{G} . \operatorname{ConnectedComponent} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.kappa_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite connected graph, a greedy step has positive dip until every color graph is connected. A finite sequence of such steps reaches an output.

**Theorem 1.11 (dip zero of connected).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) , \operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{G} \gamma \operatorname{W} \to \forall (\operatorname{e} : \operatorname{Sym2} \operatorname{V}) , \operatorname{Greedy} . \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{e} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.dip_zero_of_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite connected graph, a greedy step has positive dip until every color graph is connected. A finite sequence of such steps reaches an output.

**Theorem 1.12 (step positive).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) , \operatorname{G} . \operatorname{Connected} \to \forall (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) , (\operatorname{Coe} . \operatorname{coe} \operatorname{W}) \subseteq \operatorname{G} . \operatorname{edgeSet} \to \forall \{ \operatorname{e} : \operatorname{Sym2} \operatorname{V} \} , \operatorname{Greedy} . \operatorname{IsGreedyStep} \operatorname{G} \gamma \operatorname{W} \operatorname{e} \to 0 < \operatorname{Greedy} . \operatorname{dip} \operatorname{G} \gamma \operatorname{W} \operatorname{e}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.step_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite connected graph, a greedy step has positive dip until every color graph is connected. A finite sequence of such steps reaches an output.

**Theorem 1.13 (exists greedy output).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{G} : \operatorname{SimpleGraph} \operatorname{V}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) , \operatorname{G} . \operatorname{Connected} \to \exists \operatorname{U} , \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{U}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.exists_greedy_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite connected graph, a greedy step has positive dip until every color graph is connected. A finite sequence of such steps reaches an output.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsColorConnecting`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsGreedyOutput`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsGreedyRun`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.IsGreedyStep`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.colorEdges`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.dip`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.dip_zero_of_connected`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.exists_greedy_output`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.kappa_connected`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.potential`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.step_positive`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.wildColorGraph`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy.wildNumber`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph](AmalgamGraph.md)
