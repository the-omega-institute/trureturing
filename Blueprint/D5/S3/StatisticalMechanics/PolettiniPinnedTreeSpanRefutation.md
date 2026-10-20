# Triangle pins refute the proposed spanning-tree dimension

## Abstract

A triangle of pinned reversible edges in unit-rate K4 makes the rooted spanning-tree vectors linearly dependent.

Vertices are Fin N. The real rate r(a,b) is positive exactly on directed edges a → b. Each pinned edge has three statuses: none excludes both orientations, some true includes the forward orientation and excludes the backward orientation, and some false does the reverse. Thus functions Fin n → Option Bool index all 3ⁿ coordinates. A parent map fixes its root; its root loop contributes no rate factor.

**Definition 1.1 (Irreducibility).**

$$\forall (N: \mathbb{N}), (\forall (r: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\operatorname{Irreducible}\left(r\right) = (\forall (x: \operatorname{Fin}\left(N\right)), (\forall (y: \operatorname{Fin}\left(N\right)), (\operatorname{Relation.ReflTransGen}\left(\operatorname{fun} (a: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{fun} (b: \operatorname{Fin}\left(N\right)) \mapsto (0 < r\left(a, b\right))), x, y\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.Irreducible` (`✓ std3`).

*Citation.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

Page 6, §2.1: “We assume the graph to be irreducible, that is, there exists a path x ⇝ y of nonzero weight between any two vertices.” Relation.ReflTransGen allows a path of length zero. The edge relation tests strict positivity of r.

**Definition 1.2 (Rooted spanning trees).**

$$\forall (N: \mathbb{N}), (\forall (r: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (x: \operatorname{Fin}\left(N\right)), (\forall (p: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(N\right)), (\operatorname{IsRootedTree}\left(r, x, p\right) = ((p\left(x\right) = x) \land ((\forall (v: \operatorname{Fin}\left(N\right)), ((v \ne x) \Rightarrow (0 < r\left(v, p\left(v\right)\right)))) \land (\forall (v: \operatorname{Fin}\left(N\right)), (\exists (k: \mathbb{N}), (\left(p^{[k]}\right)\left(v\right) = x)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.IsRootedTree` (`✓ std3`).

*Citation.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

Page 6, §2.1: “In a directed graph, a rooted spanning tree Tₓ with root x is a spanning tree such that each edge is directed along the unique path that leads to the root.” The parent p(v) is the endpoint of the outgoing edge at each non-root vertex v. The root is fixed, all other parent edges have positive rate, and every vertex reaches the root after finitely many iterations.

**Definition 1.3 (An oriented tree edge).**

$$\forall (N: \mathbb{N}), (\forall (x: \operatorname{Fin}\left(N\right)), (\forall (p: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(N\right)), (\forall (u: \operatorname{Fin}\left(N\right)), (\forall (v: \operatorname{Fin}\left(N\right)), (\operatorname{Contains}\left(x, p, u, v\right) = ((u \ne x) \land (p\left(u\right) = v)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.Contains` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

For a parent map rooted at x, the arc u → v belongs to the tree precisely when u is not the root and p(u) = v. The auxiliary root loop is excluded.

**Definition 1.4 (The three statuses of a reversible edge).**

$$\forall (N: \mathbb{N}), (\forall (x: \operatorname{Fin}\left(N\right)), (\forall (p: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(N\right)), (\forall (e: \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right)), ((\operatorname{HasStatus}\left(x, p, e, \operatorname{none}\right) = ((\neg (\operatorname{Contains}\left(x, p, (e).1, (e).2\right))) \land (\neg (\operatorname{Contains}\left(x, p, (e).2, (e).1\right))))) \land ((\operatorname{HasStatus}\left(x, p, e, \operatorname{some}\left(\operatorname{true}\right)\right) = ((\operatorname{Contains}\left(x, p, (e).1, (e).2\right)) \land (\neg (\operatorname{Contains}\left(x, p, (e).2, (e).1\right))))) \land (\operatorname{HasStatus}\left(x, p, e, \operatorname{some}\left(\operatorname{false}\right)\right) = ((\operatorname{Contains}\left(x, p, (e).2, (e).1\right)) \land (\neg (\operatorname{Contains}\left(x, p, (e).1, (e).2\right))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.HasStatus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

The ordered pair e chooses the forward orientation. These three cases specify the two inclusion tests separately, so no coordinate permits both orientations of a pinned edge.

**Definition 1.5 (Conditioned rooted spanning-tree vectors).**

$$\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (r: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (pins: \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right))), (\forall (x: \operatorname{Fin}\left(N\right)), (\operatorname{tau}\left(r, pins, x\right) = \operatorname{fun} (s: \operatorname{Fin}\left(n\right) \to \operatorname{Option}\left(\operatorname{Bool}\right)) \mapsto (\sum_{p \in \operatorname{Finset.filter}\left(\operatorname{fun} (p: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(N\right)) \mapsto ((\operatorname{IsRootedTree}\left(r, x, p\right)) \land (\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{HasStatus}\left(x, p, pins\left(i\right), s\left(i\right)\right)))), \operatorname{Finset.univ}\right)} (\prod_{v \in \operatorname{Finset.erase}\left(\operatorname{Finset.univ}, x\right)} (r\left(v, p\left(v\right)\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.tau` (`✓ std3`).

*Citation.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

Page 6, Definition 1: “The conditioned rooted spanning tree polynomial is defined as” τₓ^{∖A ∖∖B} = ∑_{Tₓ : A ∩ Tₓ = ∅, B ⊆ Tₓ} r(Tₓ). For a status s, A contains both arcs of an absent pin and the excluded reverse arc of an oriented pin; B contains the chosen arcs. The displayed sum is over all parent maps satisfying these conditions, and its product ranges over all vertices except the root. The empty product is one. Every rooted tree is counted once, with weight equal to the product of its directed edge rates.

**Definition 1.6 (Deleting the pinned edges).**

$$\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (r: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (pins: \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right))), (\operatorname{deletePins}\left(r, pins\right) = \operatorname{fun} (a: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{fun} (b: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{if} (\exists (i: \operatorname{Fin}\left(n\right)), ((pins\left(i\right) = (a, b)) \lor (pins\left(i\right) = (b, a)))) \operatorname{then} 0 \operatorname{else} r\left(a, b\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.deletePins` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

Both orientations of every pinned pair receive rate zero. All other rates retain their original values.

**Definition 1.7 (The conjectured dimension).**

$$\operatorname{claim} = (\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (r: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (pins: \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right))), ((\forall (a: \operatorname{Fin}\left(N\right)), (\forall (b: \operatorname{Fin}\left(N\right)), (0 \le r\left(a, b\right)))) \Rightarrow ((\operatorname{Irreducible}\left(r\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (((pins\left(i\right)).1 \ne (pins\left(i\right)).2) \land ((0 < r\left((pins\left(i\right)).1, (pins\left(i\right)).2\right)) \land (0 < r\left((pins\left(i\right)).2, (pins\left(i\right)).1\right))))) \Rightarrow ((\operatorname{Function.Injective}\left(\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Sym2.mk}\left(pins\left(i\right)\right))\right)) \Rightarrow ((\operatorname{Irreducible}\left(\operatorname{deletePins}\left(r, pins\right)\right)) \Rightarrow (\operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{Submodule.span}\left(\mathbb{R}, \operatorname{Set.range}\left(\operatorname{tau}\left(r, pins\right)\right)\right)\right) = n + 1))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.claim` (`✓ std3`).

*Citation.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

Page 2, Introduction: “Finally, we conjecture that the 3ⁿ-vectors representing the deletion-constriction through n reversible edges span a n+1 dimensional space.” N is the number of vertices and n is the number of distinct unordered pinned edges. The statement requires nonnegative rates, irreducibility, positive rates in both directions of every pin, distinct endpoints, injectivity as Sym2 edges, and irreducibility after deleting all pins. The finrank is over ℝ of the span of the N vectors tau(r,pins,x).

**Theorem 1.8 (A pinned triangle disproves the dimension formula).**

$$\neg (\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (r: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (pins: \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right))), ((\forall (a: \operatorname{Fin}\left(N\right)), (\forall (b: \operatorname{Fin}\left(N\right)), (0 \le r\left(a, b\right)))) \Rightarrow ((\operatorname{Irreducible}\left(r\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (((pins\left(i\right)).1 \ne (pins\left(i\right)).2) \land ((0 < r\left((pins\left(i\right)).1, (pins\left(i\right)).2\right)) \land (0 < r\left((pins\left(i\right)).2, (pins\left(i\right)).1\right))))) \Rightarrow ((\operatorname{Function.Injective}\left(\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Sym2.mk}\left(pins\left(i\right)\right))\right)) \Rightarrow ((\operatorname{Irreducible}\left(\operatorname{deletePins}\left(r, pins\right)\right)) \Rightarrow (\operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{Submodule.span}\left(\mathbb{R}, \operatorname{Set.range}\left(\operatorname{tau}\left(r, pins\right)\right)\right)\right) = n + 1))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/polettini-pinned-tree-span` (refuted) by `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"polettini-pinned-tree-span","declaration_gid":"D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte (2024). *Coplanarity of rooted spanning-tree vectors*. DOI: [10.1007/s11005-025-02026-8](https://doi.org/10.1007/s11005-025-02026-8). URL: <https://arxiv.org/abs/2407.16093v1>.

*Commentary.*

Use N = 4, n = 3, rates zero on the diagonal and one elsewhere, and pins (0,1), (1,2), (2,0). Deleting these pins leaves the bidirected star centred at 3, so irreducibility holds before and after deletion. There are sixteen rooted trees for each root. Counting their twenty-seven statuses gives tau(r,pins,0) + tau(r,pins,1) + tau(r,pins,2) = 3 • tau(r,pins,3). The four vectors are therefore linearly dependent, and their span has dimension at most three, whereas n + 1 is four. The argument establishes the failure of the universal dimension formula; it does not assert a general replacement formula for arbitrary pinned graphs.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.Contains`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.HasStatus`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.Irreducible`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.IsRootedTree`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.deletePins`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.tau`
