# Refuting the unrestricted Conjecture 2

## Abstract

The full finite-graph Conjecture 2 of Boyer--Kuenzel--Lyle--Pellico is false.

**Definition 1.1 (Conjecture 2 in its complete quantified form).**

$$\mathrm{claim} \Leftrightarrow \left(\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathrm{Nat},\; 0 < k \Rightarrow \left(\left(\operatorname{Connected}\left(G\right) \land \left(\operatorname{WellHued}\left(G\right) \land \left(\operatorname{HasSequence}\left(G, k\right) \land \operatorname{HasChromaticNumber}\left(G, k\right)\right)\right)\right) \Leftrightarrow \left(\operatorname{BalancedMultipartiteSubgraph}\left(G, k\right) \land \operatorname{AntiNeighborhoodFree}\left(G\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.claim` (`✓ std3`).

*Citation.* Geoffrey Boyer, Kirsti Kuenzel, Jeremy Lyle, Ryan Pellico (2025). *Well-hued graphs with first difference two*. DOI: [10.48550/arXiv.2506.04993](https://doi.org/10.48550/arXiv.2506.04993). URL: <https://arxiv.org/abs/2506.04993v1>.

*Commentary.*

Boyer, Kuenzel, Lyle and Pellico state Conjecture 2 in Section 3, printed page 10, of arXiv:2506.04993v1. Although the surrounding section studies independence number two, this conjecture explicitly replaces two by alpha(G). The definition therefore retains every finite simple graph and every positive integer k; Theorem 4 of that paper is a separate restricted statement.

ProperColorable G j S means that a map from the vertex type to Fin j is proper on the induced set S. Each set and each extension may choose a fresh coloring. For positive j, extending a coloring outside S is unrestricted. MaximalColorable requires this property on S and its failure on every one-vertex extension. By heredity this is inclusion-maximal induced colorability, allowing recoloring. WellHued requires equal orders for every pair of such sets for every positive j. HasSequence specifies order j times the independence number for 1 <= j <= k. HasChromaticNumber requires a k-coloring and excludes every smaller number of colors.

The left side is connectedness together with these three properties. BalancedMultipartiteSubgraph means that k pairwise disjoint independent parts, each of size alpha(G), cover the vertex set. This is exactly a spanning subgraph of the balanced complete k-partite host. AntiNeighborhoodFree excludes an independent set of size alpha(G) outside each closed neighborhood: the forbidden induced graph in the source is the edgeless graph, with the overline retained. These two conditions form the right side.

**Theorem 1.2 (The 3 by 3 rook graph counterexample).**

$$\neg \left(\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathrm{Nat},\; 0 < k \Rightarrow \left(\left(\operatorname{Connected}\left(G\right) \land \left(\operatorname{WellHued}\left(G\right) \land \left(\operatorname{HasSequence}\left(G, k\right) \land \operatorname{HasChromaticNumber}\left(G, k\right)\right)\right)\right) \Leftrightarrow \left(\operatorname{BalancedMultipartiteSubgraph}\left(G, k\right) \land \operatorname{AntiNeighborhoodFree}\left(G\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Geoffrey Boyer, Kirsti Kuenzel, Jeremy Lyle, Ryan Pellico (2025). *Well-hued graphs with first difference two*. DOI: [10.48550/arXiv.2506.04993](https://doi.org/10.48550/arXiv.2506.04993). URL: <https://arxiv.org/abs/2506.04993v1>.

*Acknowledgement.* Wayne Goddard, Kirsti Kuenzel, Eileen Melville (2022). *Well-hued graphs*. DOI: [10.1016/j.dam.2022.06.010](https://doi.org/10.1016/j.dam.2022.06.010). URL: <https://people.computing.clemson.edu/~goddard/papers/wellhued.pdf>.

*Commentary.*

The graph on Fin 3 times Fin 3 joins distinct cells in a common row or column. Its independence number is three: the diagonal is independent and an independent set has at most one cell in each row. The three parts given by row plus column modulo three are independent triples, disjoint and covering the board. An independent triple outside a closed neighborhood could be enlarged by its center, contradicting the independence number. Thus the right side holds at k=3.

The set S={(0,0),(0,1),(1,0),(1,1),(2,2)} induces a four-cycle and an isolated vertex. The set T={(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)} induces a six-cycle. The proof checks proper two-colorability and failure of two-colorability for every one-vertex extension of each set, under any recoloring. Their unequal orders five and six contradict WellHued. Applying the conjectured reverse implication to this graph therefore refutes the entire quantified equivalence.

The rook-graph classification and its failure of well-huedness are due to Goddard, Kuenzel and Melville, Well-hued graphs (2022), Lemma 6 and Theorem 10. Their criterion says that K_m box K_n, for n >= m, is well-hued exactly when n >= 2(m-1); their maximal-colorability construction supplies the obstruction used here at m=n=3. These facts are credited to that source. The conclusion here connects this obstruction to the unrestricted Conjecture 2 of the 2025 paper. It establishes no corrected conjecture and makes no priority claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result`
