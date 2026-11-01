# Identity edge words on finite trees

## Abstract

Leaf intervals characterize identity words on every finite tree.

**Definition 1.1 (Noncrossing double occurrence words).**

$$\forall (n : \mathbb{N}), \forall (w : \operatorname{List}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), \operatorname{NoncrossingDoubleOccurrence}\left(w\right) \Leftrightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in w) \Rightarrow (\operatorname{List.count}\left(a, w\right) = 2)) \land (\forall (i : \operatorname{Fin}\left(\operatorname{List.length}\left(w\right)\right)), \forall (j : \operatorname{Fin}\left(\operatorname{List.length}\left(w\right)\right)), \forall (k : \operatorname{Fin}\left(\operatorname{List.length}\left(w\right)\right)), \forall (l : \operatorname{Fin}\left(\operatorname{List.length}\left(w\right)\right)), (w[i] = w[j]) \Rightarrow ((w[k] = w[l]) \Rightarrow ((w[i] \ne w[k]) \Rightarrow (\neg \operatorname{NoncrossingNonnestingGraphRecurrence.Crossing}\left((i, j), (k, l)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.NoncrossingDoubleOccurrence` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *Transposition Cayley Spectra and Subgraph Counts*. URL: <https://arxiv.org/abs/2610.14373v1>.

*Commentary.*

Page 14, Conjecture 1(iii): "For a tree T, a word of length 2|E(T)| in the edges of T using every edge has product 1 if and only if every edge occurs exactly twice and, for every vertex x of T, the subword formed by the edges incident to x is a non-crossing double occurrence word." For this term, every occurring letter has two copies. The existing Crossing predicate compares the position pairs (i,j) and (k,l); it forbids both alternating orders. Nested pairs and the empty word are allowed.

**Definition 1.2 (Shapiro's local tree criterion).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), \forall (T : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (w : \operatorname{List}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), (\operatorname{SimpleGraph.IsTree}\left(T\right)) \Rightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in w) \Rightarrow (a \in \operatorname{SimpleGraph.edgeFinset}\left(T\right))) \Rightarrow ((\operatorname{List.length}\left(w\right) = 2 \cdot \operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(T\right)\right)) \Rightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in \operatorname{SimpleGraph.edgeFinset}\left(T\right)) \Rightarrow (a \in w)) \Rightarrow (\operatorname{List.prod}\left(\operatorname{List.map}\left(\operatorname{SupportAndEdgeWordReflection.edgeSwap}, w\right)\right) = 1 \Leftrightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in \operatorname{SimpleGraph.edgeFinset}\left(T\right)) \Rightarrow (\operatorname{List.count}\left(a, w\right) = 2)) \land (\forall (x : \operatorname{Fin}\left(n\right)), \operatorname{NoncrossingDoubleOccurrence}\left(\operatorname{List.filter}\left(fun (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{decide}\left(x \in a\right), w\right)\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.claim` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *Transposition Cayley Spectra and Subgraph Counts*. URL: <https://arxiv.org/abs/2610.14373v1>.

*Commentary.*

Page 14, Conjecture 1(iii): "For a tree T, a word of length 2|E(T)| in the edges of T using every edge has product 1 if and only if every edge occurs exactly twice and, for every vertex x of T, the subword formed by the edges incident to x is a non-crossing double occurrence word." Fin n relabels the source's vertex set [n]. Sym2 represents unordered endpoint pairs. SimpleGraph.IsTree supplies connectedness and acyclicity; the two membership hypotheses say that the word contains only tree edges and uses every tree edge. List.prod multiplies the endpoint transpositions in list order, with (sigma * rho)(v) = sigma(rho(v)). List.filter retains the original order and tests decidable endpoint membership. The length is twice the edge count, including the empty word on the one-vertex tree.

**Theorem 1.3 (The local tree criterion holds).**

$$\forall (n : \mathbb{N}), \forall (T : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (w : \operatorname{List}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), (\operatorname{SimpleGraph.IsTree}\left(T\right)) \Rightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in w) \Rightarrow (a \in \operatorname{SimpleGraph.edgeFinset}\left(T\right))) \Rightarrow ((\operatorname{List.length}\left(w\right) = 2 \cdot \operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(T\right)\right)) \Rightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in \operatorname{SimpleGraph.edgeFinset}\left(T\right)) \Rightarrow (a \in w)) \Rightarrow (\operatorname{List.prod}\left(\operatorname{List.map}\left(\operatorname{SupportAndEdgeWordReflection.edgeSwap}, w\right)\right) = 1 \Leftrightarrow ((\forall (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (a \in \operatorname{SimpleGraph.edgeFinset}\left(T\right)) \Rightarrow (\operatorname{List.count}\left(a, w\right) = 2)) \land (\forall (x : \operatorname{Fin}\left(n\right)), \operatorname{NoncrossingDoubleOccurrence}\left(\operatorname{List.filter}\left(fun (a : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{decide}\left(x \in a\right), w\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.result` (`✓ std3`). ∎

*Resolves.* `Problems/shap2610` (proved) by `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shap2610","declaration_gid":"D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Boris Shapiro (2026). *Transposition Cayley Spectra and Subgraph Counts*. URL: <https://arxiv.org/abs/2610.14373v1>.

*Commentary.*

Deleting a tree edge separates its endpoints, so an identity word cannot use that edge once. The prescribed total length forces multiplicity two. For a leaf edge, the permutation between its two copies fixes its other endpoint. Cancellation replaces that interval by its singleton letters. A product of distinct forest-edge transpositions fixes exactly the vertices outside those edges, which excludes a crossing with the leaf edge. Induction proves necessity. For sufficiency, crossing edges have disjoint endpoints, their transpositions commute, and repeated pairs cancel.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.NoncrossingDoubleOccurrence`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.result`
- Dependency: [D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence](../../../../S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.md)
- Dependency: [D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection](SupportAndEdgeWordReflection.md)
