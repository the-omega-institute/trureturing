# Detour Different-Distance Numbers of Sunlets

## Abstract

The lower and upper detour different-distance numbers of every sunlet are two.

Alsinai and Ahmed ask for both numbers for sunlets in Section 4, Problem 4.3. Their Theorem 2.14(i), applied to the triangle, gives both numbers for the three-index sunlet. Their Lemma 3.4 gives the core–leaf pair at each index. The result below gives both extrema for every cycle length n at least four.

**Definition 1.1 (The graph).**

$$\forall (n:\mathbb{N}), \forall (x:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), \forall (y:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), \operatorname{Adj}\left(\operatorname{sunlet}\left(n\right), x, y\right) \iff (\operatorname{fst}\left(x\right)=\operatorname{fst}\left(y\right) \land \operatorname{snd}\left(x\right) \neq \operatorname{snd}\left(y\right)) \lor (\operatorname{snd}\left(x\right)=0 \land \operatorname{snd}\left(y\right)=0 \land \operatorname{Adj}\left(\operatorname{cycleGraph}\left(n\right), \operatorname{fst}\left(x\right), \operatorname{fst}\left(y\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

The index lies in the cycle Cₙ. At each index, the vertex of height zero is on the cycle and the vertex of height one has only the core vertex as its neighbor. For n at least three this is the corona Cₙ ∘ K₁ of Section 2.8.

**Theorem 1.2 (Distinct indices).**

$$\forall (n:\mathbb{N}), (3 \leq n) \implies \forall (i:\operatorname{Fin}\left(n\right)), \forall (j:\operatorname{Fin}\left(n\right)), (i \neq j) \implies \forall (a:\operatorname{Fin}\left(2\right)), \forall (b:\operatorname{Fin}\left(2\right)), \operatorname{IsGreatest}\left(\{L:\mathbb{N} \mid \exists (p:\operatorname{Walk}\left(\operatorname{sunlet}\left(n\right), (i,a), (j,b)\right)), \operatorname{IsPath}\left(p\right) \land \operatorname{length}\left(p\right)=L\}, \operatorname{max}\left(\operatorname{val}\left(i-j\right), \operatorname{val}\left(j-i\right)\right)+\operatorname{val}\left(a\right)+\operatorname{val}\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_isGreatest_pathLength_of_index_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

Simple walks have no repeated vertices. Removing any leaf endpoint edges leaves one of the two directed cycle arcs. Each arc extends to a simple path with the prescribed leaf endpoints. Subtraction of indices is in Fin n and val gives the residue as a natural number.

**Theorem 1.3 (A single index).**

$$\forall (n:\mathbb{N}), \forall (i:\operatorname{Fin}\left(n\right)), \forall (a:\operatorname{Fin}\left(2\right)), \forall (b:\operatorname{Fin}\left(2\right)), \operatorname{IsGreatest}\left(\{L:\mathbb{N} \mid \exists (p:\operatorname{Walk}\left(\operatorname{sunlet}\left(n\right), (i,a), (i,b)\right)), \operatorname{IsPath}\left(p\right) \land \operatorname{length}\left(p\right)=L\}, \operatorname{if} a=b \operatorname{then} 0 \operatorname{else} 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_isGreatest_pathLength_same_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

A simple path with identical endpoints is the trivial path. At unequal heights the leaf edge is the unique simple path, since leaving the leaf leads directly to its core vertex.

**Definition 1.4 (Detour distance).**

$$\forall (n:\mathbb{N}), \forall (u:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), \forall (v:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), \operatorname{detourDistance}\left(u, v\right)=\operatorname{sSup}\left(\{L:\mathbb{N} \mid \exists (p:\operatorname{Walk}\left(\operatorname{sunlet}\left(n\right), u, v\right)), \operatorname{IsPath}\left(p\right) \land \operatorname{length}\left(p\right)=L\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.detourDistance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

The greatest edge count exists by the two path-length formulas at n at least three. The trivial path gives the published zero diagonal.

**Definition 1.5 (Detour different-distance sets).**

$$\forall (n:\mathbb{N}), \forall (S:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)\right)), \operatorname{IsDDD}\left(S\right) \iff S \neq \emptyset \land S \neq \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)\right) \land (\forall (w:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), \forall (u:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), \forall (v:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)), (\neg (w \in S) \land u \in S \land v \in S \land u \neq v) \implies \operatorname{detourDistance}\left(w, u\right) \neq \operatorname{detourDistance}\left(w, v\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.IsDDD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

The set is nonempty, proper, and distinguished in detour distance by every outside vertex, as in Definition 1.1.

**Definition 1.6 (Orders of maximal sets).**

$$\forall (n:\mathbb{N}), \operatorname{maximalDDDOrders}\left(n\right)=\{m:\mathbb{N} \mid \exists (S:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)\right)), \operatorname{IsDDD}\left(S\right) \land (\forall (T:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(2\right)\right)), (\operatorname{IsDDD}\left(T\right) \land S \subseteq T) \implies T \subseteq S) \land \operatorname{card}\left(S\right)=m\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.maximalDDDOrders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

Maximality uses inclusion among all detour different-distance sets.

**Theorem 1.7 (The lower and upper numbers).**

$$\forall (n:\mathbb{N}), (4 \leq n) \implies \operatorname{sInf}\left(\operatorname{maximalDDDOrders}\left(n\right)\right)=2 \land \operatorname{sSup}\left(\operatorname{maximalDDDOrders}\left(n\right)\right)=2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_detour_numbers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ammar Alsinai and Hanan Ahmed (2026). *Detour different-distance sets in graphs*. DOI: [10.48550/arXiv.2611.26653](https://doi.org/10.48550/arXiv.2611.26653). URL: <https://arxiv.org/abs/2611.26653v1>.

*Commentary.*

A detour tie from a third index forces both vertices there into the set. Color vertices by height for odd n and by index plus height modulo two for even n. Two selected vertices of one color at different indices force a full pair via the center of a cycle arc. Any other selected index then forces a second full pair. A closest pair of full indices must be adjacent because an interior midpoint would force a closer pair. Adjacent full pairs force every index, violating properness. This bounds every DDD set by two. Each singleton extends to its core–leaf pair, so the orders of the inclusion-maximal sets form the singleton set containing two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.IsDDD`
- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.detourDistance`
- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.maximalDDDOrders`
- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet`
- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_detour_numbers`
- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_isGreatest_pathLength_of_index_ne`
- Truth anchor: `D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_isGreatest_pathLength_same_index`
