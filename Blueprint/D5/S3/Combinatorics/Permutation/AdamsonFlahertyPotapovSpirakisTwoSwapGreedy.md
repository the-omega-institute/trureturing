# The 2-swap greedy shortest-path conjecture is false

## Abstract

Binary words at distance one force arbitrarily many greedy swaps.

Words are functions Fin n → α. The paper's positions 1,…,n and alphabet 1,…,σ become zero-based finite types. A stage pairs occurrences in increasing position order before applying any of its swaps. Only unequal index pairs contribute to the length; this counts pairs even if a later application would exchange equal letters. The proposition below asks only for equality of this count with graph distance, and allows every maximal-count reference letter and every non-increasing order of the remaining letters.

**Definition 1.1 (Exchanging two positions).**

$$\forall A \in \mathit{Type},\; \forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to A,\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{twoSwap}\left(w, i, j\right) = w\circ\operatorname{Equiv}.\operatorname{swap}\left(i, j\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.twoSwap` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Definition 1, page 4: ‘Given a word w∈Σⁿ and pair i,j∈[n], i<j such that w[i]≠w[j], the 2-swap of w by (i,j), denoted w∘(i,j), returns the word w[1,i−1]w[j]w[i+1,j−1]w[i]w[j+1,n].’ Precomposition by Equiv.swap exchanges those entries; the restrictions on indices and letters appear in IsTwoSwapOf.

**Definition 1.2 (Counting each letter).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to A,\; \forall a \in A,\; \operatorname{parikh}\left(w, a\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\mathit{fun}(j:\operatorname{Fin}\left(n\right))\mapsto \operatorname{w}\left(j\right) = a, \operatorname{Finset}.\operatorname{univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.parikh` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Page 4: ‘Given a word w∈Σⁿ, the Parikh vector of w, denoted P(w) is the σ-length vector such that the ith entry of P(w) contains the number of occurrences of symbol i in w, formally, for i∈[σ], P(w)[i]=|{j∈[n] | w[j]=i}|, where n=|w|.’ The finite-set cardinality counts each position once.

**Definition 1.3 (The 2-swap relation).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to A,\; \forall v \in \operatorname{Fin}\left(n\right) \to A,\; \operatorname{IsTwoSwapOf}\left(w, v\right) = (\exists i \in \operatorname{Fin}\left(n\right),\; \exists j \in \operatorname{Fin}\left(n\right),\; (i < j) \land ((\operatorname{w}\left(i\right) \ne \operatorname{w}\left(j\right)) \land (v = \operatorname{twoSwap}\left(w, i, j\right))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.IsTwoSwapOf` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Definition 1, page 4: ‘Given a word w∈Σⁿ and pair i,j∈[n], i<j such that w[i]≠w[j], the 2-swap of w by (i,j), denoted w∘(i,j), returns the word w[1,i−1]w[j]w[i+1,j−1]w[i]w[j+1,n].’ This predicate supplies precisely the two restrictions and the resulting word.

**Definition 1.4 (The graph on all words).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \operatorname{swapGraph}\left(n, A\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left(\mathit{IsTwoSwapOf}\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.swapGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

The graph SimpleGraph.fromRel makes the 2-swap relation undirected and excludes loops. Its vertices here are all functions Fin n → α.

**Definition 1.5 (The configuration graph).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall P \in A \to \mathbb{N},\; \operatorname{configGraph}\left(P\right) = \operatorname{SimpleGraph}.\operatorname{induce}\left(\{w\mid\operatorname{parikh}\left(w\right) = P\}, \operatorname{swapGraph}\left(n, A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.configGraph` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Page 5: ‘For a given alphabet Σ and Parikh vector P, the configuration graph of Σ∗|P is the undirected graph G(P)={V(P),E(P)} where:’ The source explains: ‘Informally, the configuration graph for a given Parikh vector P is the graph with each vertex corresponding to some word in Σ∗|P, and each edge connecting every pair of words w,u∈Σ∗|P such that there exists some 2-swap transforming w into u.’ SimpleGraph.induce restricts swapGraph to exactly these words.

**Definition 1.6 (Occurrence positions in increasing order).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to A,\; \forall x \in A,\; \operatorname{occurrences}\left(w, x\right) = \operatorname{List}.\operatorname{filter}\left(\mathit{fun}(i:\operatorname{Fin}\left(n\right))\mapsto \operatorname{decide}\left((\operatorname{w}\left(i\right) = x)\right), \operatorname{List}.\operatorname{finRange}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.occurrences` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Algorithm 1, page 9: ‘i ← index of kᵗʰ occurrence of x in w’. Filtering List.finRange n by equality to x lists exactly those positions in increasing order. The source's kᵗʰ occurrence has list index k−1.

**Definition 1.7 (Pairing corresponding occurrences).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall u \in \operatorname{Fin}\left(n\right) \to A,\; \forall v \in \operatorname{Fin}\left(n\right) \to A,\; \forall x \in A,\; \operatorname{stageSwaps}\left(u, v, x\right) = \operatorname{List}.\operatorname{zip}\left(\operatorname{occurrences}\left(u, x\right), \operatorname{occurrences}\left(v, x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.stageSwaps` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Algorithm 1, page 9: ‘i ← index of kᵗʰ occurrence of x in w’ and ‘j ← index of kᵗʰ occurrence of x in v’. List.zip pairs corresponding entries of the two occurrence lists. For equal Parikh vectors their lengths agree.

**Definition 1.8 (Applying a stage).**

$$\forall A \in \mathit{Type},\; \forall n \in \mathbb{N},\; \forall u \in \operatorname{Fin}\left(n\right) \to A,\; \forall S \in \operatorname{List}\left((\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\right),\; \operatorname{applySwaps}\left(u, S\right) = \operatorname{List}.\operatorname{foldl}\left(\mathit{fun}(c:\operatorname{Fin}\left(n\right) \to A)\mapsto \mathit{fun}(p:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\mapsto c\circ\operatorname{Equiv}.\operatorname{swap}\left(p.1, p.2\right), u, S\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.applySwaps` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Algorithm 1, page 9: ‘Apply all 2-swaps in S to w and set S ← ∅’. List.foldl applies them in increasing occurrence order. The length comparison below does not assume that this application reaches the target word.

**Definition 1.9 (The sequence of stages).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(n\right) \to A,\; \begin{aligned}\forall u \in \operatorname{Fin}\left(n\right) \to A,\; \operatorname{greedySwaps}\left(v, [], u\right) = []\\\forall x \in A,\; \forall t \in \operatorname{List}\left(A\right),\; \forall u \in \operatorname{Fin}\left(n\right) \to A,\; \operatorname{greedySwaps}\left(v, (x::t), u\right) = \operatorname{List}.\operatorname{append}\left(\operatorname{stageSwaps}\left(u, v, x\right), \operatorname{greedySwaps}\left(v, t, \operatorname{applySwaps}\left(u, \operatorname{stageSwaps}\left(u, v, x\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.greedySwaps` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Algorithm 1, page 9: ‘for x ∈ Σ \ {1} do’. The empty list performs no stage. A nonempty list first records the occurrence pairs for its head letter, then continues from the word obtained by applying those pairs.

**Definition 1.10 (Counting nontrivial pairs).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],\forall n \in \mathbb{N},\; \forall o \in \operatorname{List}\left(A\right),\; \forall w \in \operatorname{Fin}\left(n\right) \to A,\; \forall v \in \operatorname{Fin}\left(n\right) \to A,\; \operatorname{greedyLength}\left(o, w, v\right) = \operatorname{List}.\operatorname{length}\left(\operatorname{List}.\operatorname{filter}\left(\mathit{fun}(p:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right))\mapsto \operatorname{decide}\left((p.1 \ne p.2)\right), \operatorname{greedySwaps}\left(v, o, w\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.greedyLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

A nontrivial pair has distinct position indices. Filtering by that predicate and taking List.length gives the count compared with SimpleGraph.dist. Pairs are counted before imposing any condition on the letters when the pair is eventually applied.

**Definition 1.11 (Permitted reference letters and orders).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)],[\operatorname{Fintype}\left(A\right)],\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to A,\; \forall o \in \operatorname{List}\left(A\right),\; \operatorname{AdmissibleOrder}\left(w, o\right) = (\exists r \in A,\; (\forall a \in A,\; \operatorname{parikh}\left(w, a\right) \le \operatorname{parikh}\left(w, r\right)) \land ((\operatorname{List}.\operatorname{Nodup}\left(o\right)) \land ((\neg (r \in o)) \land ((\forall a \in A,\; (a \ne r) \Rightarrow (a \in o)) \land (\operatorname{List}.\operatorname{Pairwise}\left(\mathit{fun}(a:A)\mapsto \mathit{fun}(b:A)\mapsto \operatorname{parikh}\left(w, b\right) \le \operatorname{parikh}\left(w, a\right), o\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.AdmissibleOrder` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Proof of Lemma 4, page 9: ‘We assume, without loss of generality, that P[1]≥P[2]≥⋯≥P[σ].’ Algorithm 1 runs over Σ \ {1}. The existential reference letter has maximal count. The list has no duplicates, omits that letter, contains every other letter, and has non-increasing counts. Thus all choices among ties are included.

**Definition 1.12 (The shortest-path conjecture).**

$$\mathit{claim} = (\forall s \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(s\right),\; \forall v \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(s\right),\; \forall h \in \operatorname{parikh}\left(v\right) = \operatorname{parikh}\left(w\right),\; \exists o \in \operatorname{List}\left(\operatorname{Fin}\left(s\right)\right),\; (\operatorname{AdmissibleOrder}\left(w, o\right)) \land (\operatorname{greedyLength}\left(o, w, v\right) = \operatorname{SimpleGraph}.\operatorname{dist}\left(\operatorname{configGraph}\left(\operatorname{parikh}\left(w\right)\right), \langle w,\mathit{rfl}\rangle, \langle v,h\rangle\right)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.claim` (`✓ std3`).

*Citation.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

Section 5, page 23: ‘For the 2-swap graph specifically, we leave open the problem of determining the shortest path between two given words w and v. We conjecture that the simple greedy algorithm used to derive the upper bound in Lemma 4 can be used to find the shortest path between any pair of vertices.’ The formula permits any alphabet size σ and word length n, any two words with the same Parikh vector, and any permitted letter order. The proof h puts the target word in the same configuration graph. It asks only for equality of the count with the distance; reaching the target and legality of every generated pair are additional requirements of a path.

**Theorem 1.13 (Refutation by an unbounded binary family).**

$$\neg (\forall s \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(s\right),\; \forall v \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(s\right),\; \forall h \in \operatorname{parikh}\left(v\right) = \operatorname{parikh}\left(w\right),\; \exists o \in \operatorname{List}\left(\operatorname{Fin}\left(s\right)\right),\; (\operatorname{AdmissibleOrder}\left(w, o\right)) \land (\operatorname{greedyLength}\left(o, w, v\right) = \operatorname{SimpleGraph}.\operatorname{dist}\left(\operatorname{configGraph}\left(\operatorname{parikh}\left(w\right)\right), \langle w,\mathit{rfl}\rangle, \langle v,h\rangle\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.result` (`✓ std3`). ∎

*Resolves.* `Problems/adamson-flaherty-potapov-spirakis-2023-two-swap-greedy` (refuted) by `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"adamson-flaherty-potapov-spirakis-2023-two-swap-greedy","declaration_gid":"D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis (2024). *Structural and Combinatorial Properties of 2-swap Word Permutation Graphs*. DOI: [10.1007/978-3-031-55601-2_5](https://doi.org/10.1007/978-3-031-55601-2_5). URL: <https://arxiv.org/abs/2307.01648v3>.

*Commentary.*

For each k≥2, take w=0ᵏ1ᵏ and v=1·0ᵏ⁻¹·1ᵏ⁻¹·0. Each letter occurs k times in both words. Exchanging positions 0 and 2k−1 turns w into v, so their distance is one. Pairing the zero occurrences moves every occurrence, and pairing the one occurrences also moves every occurrence: either permitted binary order therefore generates k nontrivial pairs. This proves failure throughout an unbounded family; k=2 contradicts the quantified proposition. The argument determines neither a shortest-path algorithm for unrestricted alphabets nor its complexity.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.AdmissibleOrder`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.IsTwoSwapOf`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.applySwaps`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.configGraph`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.greedyLength`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.greedySwaps`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.occurrences`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.parikh`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.stageSwaps`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.swapGraph`
- Truth anchor: `D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.twoSwap`
