# Integrality obstruction to the exact Wang–Tian strong-digraph formula

## Abstract

The unrestricted exact eventual formula for the maximum number of arcs in a saturated strict digraph fails at connectivity three and arbitrarily large odd orders.

All graphs are finite strict directed graphs. Arcs are ordered pairs of distinct vertices; opposite arcs can both occur. A host arc set has the full vertex carrier Fin n. A subdigraph has its own vertex subset and an independent arc subset, and may retain isolated vertices. Named operations below denote the displayed definitions, with the ambient n inferred when it is implicit in Lean. The functions fst and snd project the underlying ordered pair of an arc; card is finite cardinality. The proof components of the minimum and maximum are included in their dependent types.

**Definition 1.1 (Permissible ordered arcs).**

$$\forall n \in \mathbb{N},\; \mathrm{Arc}\left(n\right) = \{p: \mathrm{Fin}\left(n\right) \times \mathrm{Fin}\left(n\right) | \mathrm{fst}\left(p\right) \ne \mathrm{snd}\left(p\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Arc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Arc n is the subtype of Fin n x Fin n with unequal coordinates. Each ordered pair appears at most once in a finite arc set; reversing the pair gives a separate permissible arc.

**Definition 1.2 (Subdigraph records).**

$$\forall n \in \mathbb{N},\; \mathrm{Digraph}\left(n\right) := \{vertices: \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right); arcs: \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right); endpoints: \forall e \in \mathrm{Arc}\left(n\right),\; (e \in arcs) \Rightarrow ((\mathrm{fst}\left(e\right) \in vertices) \land (\mathrm{snd}\left(e\right) \in vertices))\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Digraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Digraph n is the record with precisely the displayed three fields, including the endpoint proof. There is no induced-subgraph requirement: deleting extra arcs or retaining isolated vertices is allowed. The field names in the record signature bind its subsequent field types.

**Definition 1.3 (The vertex field).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \mathrm{vertices}\left(H\right): \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.vertices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

The vertex field is any finite subset of Fin n. It need not be the endpoints of the arc field.

**Definition 1.4 (The arc field).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \mathrm{arcs}\left(H\right): \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.arcs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

The arc field is a finite set of permissible directed arcs whose endpoints satisfy the next field.

**Definition 1.5 (The endpoint proof field).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \forall e \in \mathrm{Arc}\left(n\right),\; (e \in \mathrm{arcs}\left(H\right)) \Rightarrow ((\mathrm{fst}\left(e\right) \in \mathrm{vertices}\left(H\right)) \land (\mathrm{snd}\left(e\right) \in \mathrm{vertices}\left(H\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.endpoints` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

For each arc in the record, both coordinates belong to its vertex set. This proof field is part of the structure, rather than an additional graph axiom.

**Definition 1.6 (Directed adjacency).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \forall a \in \mathrm{Fin}\left(n\right),\; \forall b \in \mathrm{Fin}\left(n\right),\; (\mathrm{Adj}\left(H, a, b\right)) \Leftrightarrow (\exists e \in \mathrm{Arc}\left(n\right),\; (e \in \mathrm{arcs}\left(H\right)) \land (\mathrm{val}\left(e\right) = (a, b)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Adj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Adjacency means that an arc in H has exactly the given ordered endpoints.

**Definition 1.7 (Vertex-simple directed paths).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \forall a \in \mathrm{Fin}\left(n\right),\; \forall b \in \mathrm{Fin}\left(n\right),\; (\mathrm{Dipath}\left(H, a, b\right)) \Leftrightarrow (\exists l \in \mathrm{List}\left(\mathrm{Fin}\left(n\right)\right),\; (\mathrm{Nodup}\left(\mathrm{cons}\left(a, l\right)\right)) \land ((\forall v \in \mathrm{Fin}\left(n\right),\; (v \in \mathrm{cons}\left(a, l\right)) \Rightarrow (v \in \mathrm{vertices}\left(H\right))) \land ((\mathrm{IsChain}\left(\mathrm{Adj}\left(H\right), \mathrm{cons}\left(a, l\right)\right)) \land (\mathrm{getLast}\left(\mathrm{cons}\left(a, l\right)\right) = b))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Dipath` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

The nonempty list a::l has no repeated vertices, every vertex lies in H.vertices, consecutive vertices satisfy H.Adj in the listed direction, and its final vertex is b. The getLast proof argument is the canonical proof that a cons list is nonempty; it contributes no additional condition.

**Definition 1.8 (Strong connectivity).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; (\mathrm{Strong}\left(H\right)) \Leftrightarrow (\forall a \in \mathrm{Fin}\left(n\right),\; (a \in \mathrm{vertices}\left(H\right)) \Rightarrow (\forall b \in \mathrm{Fin}\left(n\right),\; (b \in \mathrm{vertices}\left(H\right)) \Rightarrow ((a \ne b) \Rightarrow (\mathrm{Dipath}\left(H, a, b\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Strong` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Quantifying ordered distinct endpoints requires paths in both directions. The predicate is vacuous on empty and singleton records; positive strong connectivity below explicitly excludes the empty record.

**Definition 1.9 (Vertex deletion).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \forall S \in \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right),\; (\mathrm{vertices}\left(\mathrm{delete}\left(H, S\right)\right) = \mathrm{vertices}\left(H\right) \setminus S) \land (\mathrm{arcs}\left(\mathrm{delete}\left(H, S\right)\right) = \{e: \mathrm{Arc}\left(n\right) | (e \in \mathrm{arcs}\left(H\right)) \land ((\neg (\mathrm{fst}\left(e\right) \in S)) \land (\neg (\mathrm{snd}\left(e\right) \in S)))\})$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.delete` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Deletion restricts the original vertices and arcs. Its endpoint proof follows from H.endpoints and the two nonmembership conditions, so the result is again a Digraph n. The difference is finite-set difference, not arithmetic subtraction.

**Definition 1.10 (Separators, including trivial remainders).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \forall S \in \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right),\; (\mathrm{Separator}\left(H, S\right)) \Leftrightarrow ((S \subseteq \mathrm{vertices}\left(H\right)) \land ((\neg (\mathrm{Strong}\left(\mathrm{delete}\left(H, S\right)\right))) \lor (\mathrm{card}\left(\mathrm{vertices}\left(\mathrm{delete}\left(H, S\right)\right)\right) = 1)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Separator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

A separator is a subset of the original vertices whose deletion leaves a graph that is not strongly connected or has exactly one vertex. Trivial means singleton. Removing all vertices does not count via the singleton alternative.

**Definition 1.11 (The actual finite separator-size family).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \mathrm{separatorCards}\left(H\right) = \mathrm{image}\left(card, \{S: \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right) | (S \in \mathrm{powerset}\left(\mathrm{vertices}\left(H\right)\right)) \land (\mathrm{Separator}\left(H, S\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.separatorCards` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Take every subset of H.vertices, keep exactly the separators, then take their cardinalities. If H is nonempty, erasing one chosen vertex from H.vertices leaves a singleton and supplies a member of this family.

**Definition 1.12 (An attained minimum with its full certificate).**

$$\forall n \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; \forall (h: \mathrm{Nonempty}\left(\mathrm{vertices}\left(H\right)\right)), \begin{aligned}\mathrm{connectivity}\left(H, h\right): \{m: \mathbb{N} | (\exists S \in \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right),\; (\mathrm{Separator}\left(H, S\right)) \land (\mathrm{card}\left(S\right) = m)) \land (\forall S \in \mathrm{Finset}\left(\mathrm{Fin}\left(n\right)\right),\; (\mathrm{Separator}\left(H, S\right)) \Rightarrow (m \le \mathrm{card}\left(S\right)))\}\\\mathrm{val}\left(\mathrm{connectivity}\left(H, h\right)\right) = \mathrm{minPrime}\left(\mathrm{separatorCards}\left(H\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.connectivity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Nonempty T means there exists a vertex in T. The value is min' of separatorCards, with its nonemptiness proof supplied by the singleton remainder. The subtype retains an actual minimizing separator and the inequality against every separator. The displayed value equation uses min' only on this proved nonempty family; there is no default for an empty family.

**Definition 1.13 (Positive strong connectivity and the empty-domain convention).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall H \in \mathrm{Digraph}\left(n\right),\; (\mathrm{KStrong}\left(k, H\right)) \Leftrightarrow (\exists (h: \mathrm{Nonempty}\left(\mathrm{vertices}\left(H\right)\right)), k \le \mathrm{val}\left(\mathrm{connectivity}\left(H, h\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.KStrong` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

The existential h is a proof of vertex nonemptiness. Thus even a vacuously strongly connected empty record is excluded. The minimum certificate applied to the singleton remainder gives k+1 <= card(H.vertices) whenever KStrong k H. This matches the size consequence used in the source's Lemma 2.2.

**Definition 1.14 (Arbitrary forbidden subdigraphs).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right),\; (\mathrm{Forbidden}\left(k, A\right)) \Leftrightarrow (\exists H \in \mathrm{Digraph}\left(n\right),\; (\mathrm{arcs}\left(H\right) \subseteq A) \land (\mathrm{KStrong}\left(k, H\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Forbidden` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

The quantified record H chooses both a vertex subset and an arc subset. Its endpoint field puts all its arcs on those vertices. Inclusion in the full host A imposes neither spanning nor induced containment.

**Definition 1.15 (Forbidden-free hosts).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right),\; (\mathrm{Free}\left(k, A\right)) \Leftrightarrow (\neg (\mathrm{Forbidden}\left(k, A\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Free` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

A host is free precisely when no arbitrary subdigraph is k-strong.

**Definition 1.16 (Every missing permissible arc creates a forbidden subdigraph).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall A \in \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right),\; (\mathrm{Saturated}\left(k, A\right)) \Leftrightarrow ((\mathrm{Free}\left(k, A\right)) \land (\forall e \in \mathrm{Arc}\left(n\right),\; (\neg (e \in A)) \Rightarrow (\mathrm{Forbidden}\left(k, \mathrm{insert}\left(e, A\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Saturated` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Saturation includes freeness and quantifies every missing ordered arc. A reverse arc is tested independently even when its opposite is already present.

**Definition 1.17 (The finite family of all saturated hosts).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \mathrm{saturatedFamily}\left(k, n\right) = \{A: \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right) | (A \in \mathrm{powerset}\left(\mathrm{univ}\left(\mathrm{Arc}\left(n\right)\right)\right)) \land (\mathrm{Saturated}\left(k, A\right))\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.saturatedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

For positive k the empty arc set is free: a k-strong forbidden record would have at least two vertices, while empty adjacency cannot connect distinct vertices. Maximizing cardinality among all free arc sets gives a saturated set, because inserting a missing arc strictly increases cardinality. If n <= k, every graph is free and the complete arc set is saturated, including n=0. Hence the displayed finite saturated family is nonempty for every positive k and every n.

**Definition 1.18 (The actual attained extremal arc number).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall (hk: 1 \le k), \begin{aligned}\mathrm{extremum}\left(k, n, hk\right): \{m: \mathbb{N} | (\exists A \in \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right),\; (\mathrm{Saturated}\left(k, A\right)) \land (\mathrm{card}\left(A\right) = m)) \land (\forall B \in \mathrm{Finset}\left(\mathrm{Arc}\left(n\right)\right),\; (\mathrm{Saturated}\left(k, B\right)) \Rightarrow (\mathrm{card}\left(B\right) \le m))\}\\\mathrm{val}\left(\mathrm{extremum}\left(k, n, hk\right)\right) = \mathrm{maxPrime}\left(\mathrm{image}\left(card, \mathrm{saturatedFamily}\left(k, n\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.extremum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Let C be the image of card on saturatedFamily k n. It is finite and nonempty by the preceding maximal-free construction. The value of extremum is C.max'. Its subtype contains an actual saturated host attaining that value and domination over every saturated host. Nonempty refers to the family of hosts, not a requirement that n be positive; the full eventual claim and its contradicting witnesses use positive orders.

**Definition 1.19 (The full unrestricted eventual equality).**

$$claim = \left(\forall k \in \mathbb{N},\; \forall (hk: 1 \le k), \exists N \in \mathbb{N},\; \forall n \in \mathbb{N},\; (N \le n) \Rightarrow ((\mathrm{val}\left(\mathrm{extremum}\left(k, n, hk\right)\right): \mathbb{Q}) = \frac{3}{2} \cdot ((k: \mathbb{Q}) - \frac{4}{3}) \cdot ((n: \mathbb{Q}) - (k: \mathbb{Q}) + 1) + (\mathrm{choose}\left(n, 2\right): \mathbb{Q}))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

This is the complete positive-k reading of Conjecture 1 in Section 4, printed PDF page 13 of arXiv:2605.01269v1. The threshold may depend on k. The symbol hk is the proof of 1 <= k required by the actual extremum definition. All casts, divisions and subtractions in the equality are rational; choose is the natural binomial coefficient before casting. The printed conjecture has no floor, ceiling, divisibility restriction or error term. The refutation also applies to the local k >= 2 reading because it uses k=3.

**Theorem 1.20 (No threshold satisfies the full exact formula).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Qinglin Wang; Yingzhi Tian (2026). *Extremal Problems for the Family of k-Strongly Connected Digraphs*. DOI: [10.48550/arXiv.2605.01269](https://doi.org/10.48550/arXiv.2605.01269). URL: <https://arxiv.org/abs/2605.01269v1>.

*Commentary.*

Assume the whole claim and use k=3. For any threshold N choose n=2N+5, which is at least N and at least five. Clearing denominator two in the rational equality gives 2 ex = 2 choose(2N+5,2) + 5(2N+3) = 2(choose(2N+5,2)+5N+7)+1. Both ex and choose are natural numbers. Injectivity of the natural-to-rational cast therefore equates an even natural with an odd natural, a contradiction. No value of an extremizer is assumed or calculated.

This repository-derived argument concerns the literal exact unrestricted formula. It does not determine a corrected divisible-order, rounded, upper-bound or asymptotic statement. The source's construction theorem and other bounds are not assumed as axioms. The source note distinguishes the new conjecture from the related undirected Mader upper-bound literature; no global priority assertion is made.

For an arbitrary n-element finite vertex carrier W and a bijection f:W -> Fin n, send an ordered arc (u,v) to (f(u),f(v)). Injectivity preserves unequal endpoints, and the inverse bijection gives the inverse arc map. Map vertex subsets and arc subsets by these bijections; endpoint membership, arbitrary containment, insertion of a missing arc and cardinality are preserved. Map every vertex in a path list by f: list membership, nonrepetition, directed consecutive adjacency and the final endpoint are preserved, with the inverse list map proving the converse. Images under f commute with vertex-set difference, and the corresponding arc filter is exactly deletion of both endpoints. Thus the not-strong and singleton alternatives for separators correspond, and separator cardinalities and their attained minimum agree. The empty vertex set remains empty. Consequently forbiddenness, freeness and saturation correspond in both directions, and the sets of saturated arc counts, including their attained maximum, agree. This explains the labelled presentation at the definition level. No separate Lean transport theorem between two graph APIs is asserted; all formal objects here are directly on Fin n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Adj`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Arc`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Digraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Dipath`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Forbidden`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Free`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.KStrong`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Saturated`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Separator`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.Strong`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.arcs`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.connectivity`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.delete`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.endpoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.extremum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.saturatedFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.separatorCards`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.vertices`
