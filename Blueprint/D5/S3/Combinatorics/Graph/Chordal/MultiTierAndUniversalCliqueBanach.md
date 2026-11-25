# Multi-tier and universal-core gain potentials

## Abstract

Sharper gain reconstruction from predecessor sizes and universal cores.

**Theorem 1.1 (Multi-tier predecessor averaging).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{IsChordal}\left(G\right)) \Rightarrow (\forall k \in \mathbb{N},\; (4 \le k) \Rightarrow ((\forall s \in \operatorname{Finset}\left(V\right),\; (\operatorname{IsClique}\left(G, \operatorname{toSet}\left(s\right)\right)) \Rightarrow (\operatorname{card}\left(s\right) \le k+1)) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)+\operatorname{g}\left(j, l\right)-\operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)-(\operatorname{phi}\left(j\right)-\operatorname{phi}\left(i\right))\right) \le (4-\frac{4 \cdot (\operatorname{real}\left(k\right)-2)}{\operatorname{real}\left(k\right)^{2}-3 \cdot \operatorname{real}\left(k\right)+3}) \cdot epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach.exists_multitier_clique_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function real casts a natural number to a real, toSet takes the underlying set of a finset, and norm denotes the seminorm of E.

Root each connected component. In any predecessor clique, the vertices with at least s predecessors themselves have nested predecessor sets. If that collection is nonempty, its union with a smallest common predecessor set is a disjoint clique. Thus the collection has at most k + 1 − s vertices.

Use the profile 1/n for positive sizes n up to k − 2, and use the two smaller values (k − 2)/D and (k − 3)/D at k − 1 and k, where D is k squared minus 3k plus 3. A row gives each predecessor at least the row profile and at least twice the middle profile minus that predecessor's own profile. The counts at thresholds k and k − 1 bound the total preliminary weight by one. Distribute any unused weight uniformly.

Transport along the shadow anchors and average the paths through the predecessors. Across layers, the reference path has a matching term in each mean, and their combined weights save twice the middle profile in distinguished mass. Within a layer, each predecessor in the smaller clique has a matching term in the larger clique. Its error costs one triangle defect and every other term costs at most three. For k equal to four the resulting coefficient is 20/7.

**Theorem 1.2 (Simplicial attachments to a universal core).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; [\operatorname{Finite}\left(V\right)] , \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{Set}\left(V\right),\; \forall U \in \operatorname{Set}\left(V\right),\; (U \subseteq H) \Rightarrow ((\operatorname{Nonempty}\left(U\right)) \Rightarrow ((\forall u \in V,\; (u \in U) \Rightarrow (\forall h \in V,\; (h \in H) \Rightarrow ((u \ne h) \Rightarrow (\operatorname{Adj}\left(G, u, h\right))))) \Rightarrow ((\operatorname{IsIndepSet}\left(G, \operatorname{complement}\left(H\right)\right)) \Rightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\forall o \in V,\; (o \in \operatorname{complement}\left(H\right)) \Rightarrow ((\operatorname{neighbors}\left(G, o\right) \subseteq H) \land ((\operatorname{IsClique}\left(G, \operatorname{neighbors}\left(G, o\right)\right)) \land (\operatorname{ncard}\left(\operatorname{neighbors}\left(G, o\right)\right) \le m)))) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in V \to \left(V \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in V,\; \forall j \in V,\; \forall l \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow ((\operatorname{Adj}\left(G, j, l\right)) \Rightarrow ((\operatorname{Adj}\left(G, i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)+\operatorname{g}\left(j, l\right)-\operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in V \to E,\; \forall i \in V,\; \forall j \in V,\; (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)-(\operatorname{phi}\left(j\right)-\operatorname{phi}\left(i\right))\right) \le (\operatorname{max}\left(1, 2-\frac{2}{\operatorname{real}\left(m\right)}\right)) \cdot epsilon))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach.exists_universal_core_simplicial_banach_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set neighbors(G, o) consists of the vertices adjacent to o. Here ncard counts a finite set and complement is relative to V.

On the core H, average the gains from all universal vertices in U. Every residual on a core edge is an average of triangle defects with zero contributions from any endpoints in U.

For an outside vertex o with neighbors, average the candidate values obtained by extending the potential from each neighbor along its edge to o. The candidates of two distinct neighbors differ by at most twice the tolerance, from the core edge residual and the triangle through o. The self-term vanishes, giving the factor 2 − 2 divided by the number of neighbors. An isolated outside vertex receives zero.

**Theorem 1.3 (Reconstruction on the bridged gadget).**

$$\forall v \in \operatorname{Universe}\left(\right),\; \forall m \in \mathbb{N},\; \forall N \in \mathbb{N},\; (2 \le m) \Rightarrow ((1 \le N) \Rightarrow (\forall E \in \operatorname{Type}\left(v\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] , \forall g \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right) \to \left(\operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right) \to E\right),\; \forall epsilon \in \mathbb{R},\; (0 \le epsilon) \Rightarrow ((\forall i \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; \forall j \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; \operatorname{g}\left(j, i\right) = -\operatorname{g}\left(i, j\right)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; \forall j \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; \forall l \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; (\operatorname{Adj}\left(\operatorname{bridgedGadget}\left(m, N\right), i, j\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{bridgedGadget}\left(m, N\right), j, l\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{bridgedGadget}\left(m, N\right), i, l\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)+\operatorname{g}\left(j, l\right)-\operatorname{g}\left(i, l\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right) \to E,\; \forall i \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; \forall j \in \operatorname{Fin}\left(N\right) \times \operatorname{GadgetVertex}\left(m\right),\; (\operatorname{Adj}\left(\operatorname{bridgedGadget}\left(m, N\right), i, j\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(i, j\right)-(\operatorname{phi}\left(j\right)-\operatorname{phi}\left(i\right))\right) \le (2-\frac{2}{\operatorname{real}\left(m\right)}) \cdot epsilon))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach.bridgedGadget_banach_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In each copy, remove the root to obtain the core and take the u-clique as its universal set. The root attaches to the m-clique of a-vertices, so the core extension gives the coefficient 2 − 2/m.

Translate each copy by a common potential increment determined by the gains on the preceding root bridges. The translation preserves intra-copy residuals and gives zero residual on every bridge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach.bridgedGadget_banach_upper_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach.exists_multitier_clique_banach_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach.exists_universal_core_simplicial_banach_potential`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions](TwoStepBFSAndBarycenterObstructions.md)
