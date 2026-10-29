# Ordinary Amoeba Extensions and Total-Edge Growth

## Abstract

Simultaneous extensions inside finite tree hosts imply deadness for every minimum-total-edge growth. A finite interval argument supplies a safe branching degree.

The source is Gurvich, Krnc and Vyalyi, Growing Trees and Amoebas’ Replications, arXiv:2401.07484v1/v2, DOI 10.1007/s00025-025-02421-6, Section 2 and Conjecture 1. The predicates here are formal encodings of its ordinary finite-tree conventions. H is a finite simple undirected tree and m assigns a nonnegative integer to each vertex. The number of roots is the sum of m, including multiplicity. A Host packages a finite vertex type, its simple graph and connectedness and acyclicity. Copy means an injective graph homomorphism, so its image is an actual subgraph isomorphic to H. Different copy maps retain different placements of m. Containment is expressed by an injective homomorphism, allowing vertex relabeling. Coincidence is tested against that very containing map, rather than against an unrelated isomorphism: it must cover all vertices and reflect every edge. Thus no additional vertex or edge can remain outside the original containing image. The finite host convention is supported by the published Lemma 3 and Theorem 4 and by the directly cited predecessor Avoidability beyond paths, DOI 10.37236/13023, Section 2; the main paper gives no blanket sentence declaring all graphs finite.

**Definition 1.1 (All arms are present simultaneously).**

$$\forall V \in \mathrm{Type},\; \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall W \in \mathrm{Type},\; \forall G \in \mathrm{SimpleGraph}\left(W\right),\; \forall c \in \mathrm{Copy}\left(H, G\right),\; (\mathrm{HasExtension}\left(m, l, c\right)) \Leftrightarrow (\exists e \in \mathrm{Copy}\left(\mathrm{extensionGraph}\left(H, m, l\right), G\right),\; \forall v \in V,\; \mathrm{e}\left(\mathrm{inl}\left(v\right)\right) = \mathrm{c}\left(v\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.HasExtension` (`✓ std3`).

*Citation.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

The extension graph has the original vertices and new vertices (v,a,j), with a below m(v) and j below l. Original edges are preserved, v is adjacent to (v,a,0), and consecutive j values on each arm are adjacent. An injective homomorphism of this entire graph, agreeing with the prescribed copy on H, realizes every arm together. It forces all new vertices outside the copy and mutually distinct. Each arm has l edges; for l=0 it has no new vertices.

**Definition 1.2 (The objective counts total edges).**

$$\forall V \in \mathrm{Type},\; \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall G \in \mathrm{Host},\; \forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(G\right)\right),\; \forall S \in \mathrm{Host},\; \forall i \in \mathrm{Copy}\left(\mathrm{graph}\left(G\right), \mathrm{graph}\left(S\right)\right),\; (\mathrm{MinimumGrowth}\left(m, l, c, i\right)) \Leftrightarrow ((\mathrm{HasExtension}\left(m, l, \mathrm{comp}\left(i, c\right)\right)) \land (\forall R \in \mathrm{Host},\; \forall j \in \mathrm{Copy}\left(\mathrm{graph}\left(G\right), \mathrm{graph}\left(R\right)\right),\; (\mathrm{HasExtension}\left(m, l, \mathrm{comp}\left(j, c\right)\right)) \Rightarrow (\mathrm{edgeCount}\left(S\right) \le \mathrm{edgeCount}\left(R\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.MinimumGrowth` (`✓ std3`).

*Citation.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

For a specified copy c in G and containing map i into S, the extension must be realized in S over i composed with c. Every competing finite tree R and every containing map j are compared using the total number of edges. No choice of a preferred minimizer or number of newly added edges is substituted.

**Definition 1.3 (Every minimizing growth coincides).**

$$\forall V \in \mathrm{Type},\; \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall G \in \mathrm{Host},\; \forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(G\right)\right),\; (\mathrm{Dead}\left(m, l, c\right)) \Leftrightarrow (\forall S \in \mathrm{Host},\; \forall i \in \mathrm{Copy}\left(\mathrm{graph}\left(G\right), \mathrm{graph}\left(S\right)\right),\; (\mathrm{MinimumGrowth}\left(m, l, c, i\right)) \Rightarrow (\mathrm{Coincides}\left(i\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.Dead` (`✓ std3`).

*Citation.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

Coincides(i) says that i is surjective on vertices and reflects adjacency as well as preserving it. Thus it identifies the entire containing tree with the original host. Deadness quantifies all minimizing hosts and containing maps.

**Definition 1.4 (Every initial tree has a confining supertree).**

$$\forall V \in \mathrm{Type},\; \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; (\mathrm{TotallyConfined}\left(H, m, l\right)) \Leftrightarrow (\forall T \in \mathrm{Host},\; (\mathrm{Nonempty}\left(\mathrm{Copy}\left(H, \mathrm{graph}\left(T\right)\right)\right)) \Rightarrow (\exists S \in \mathrm{Host},\; (\mathrm{Nonempty}\left(\mathrm{Copy}\left(\mathrm{graph}\left(T\right), \mathrm{graph}\left(S\right)\right)\right)) \land (\mathrm{Confining}\left(H, m, l, S\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.TotallyConfined` (`✓ std3`).

*Citation.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

A confining host admits a copy and every copy in it is dead, with multiplicities transported by that copy map. Total confinement starts with any finite tree admitting a copy, preserves that initial tree by an injective graph map, and requires a confining finite host. All lengths and zero multiplicities are retained. This definition states the target property; the two lemmas below do not establish its universal existence assertion.

**Theorem 1.5 (An existing extension kills every minimum growth).**

$$\forall V \in \mathrm{Type},\; \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall G \in \mathrm{Host},\; \forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(G\right)\right),\; (\mathrm{HasExtension}\left(m, l, c\right)) \Rightarrow (\mathrm{Dead}\left(m, l, c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.dead_of_hasExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

The current host itself competes in the total-edge minimum. A minimizing containing tree therefore has at most as many edges. A finite tree has one fewer edge than vertices, so the containing map must be surjective. Its injective map on undirected edge sets is also surjective, which supplies adjacency reflection. This proves the assertion for every minimizer, including the zero-length and zero-multiplicity cases.

**Theorem 1.6 (A degree outside every demand interval).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall d \in V \to \mathrm{Nat},\; \forall m \in V \to \mathrm{Nat},\; \exists q \in \mathrm{Nat},\; (2 \le q) \land ((q \le \mathrm{sum}\left(m\right) + 2) \land (\forall v \in V,\; (\mathrm{d}\left(v\right) \le q) \Rightarrow (\mathrm{d}\left(v\right) + \mathrm{m}\left(v\right) \le q)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.exists_safe_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

The union of the integer intervals from d(v) inclusive to d(v)+m(v) exclusive has size at most the sum k of m. There are k+1 integers from 2 through k+2. One avoids the union. Whenever d(v) is at most that integer q, avoiding the interval implies d(v)+m(v) is at most q. This supplies a branching capacity, and asserts neither the construction of a host nor disjoint path existence.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.Dead`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.HasExtension`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.MinimumGrowth`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.TotallyConfined`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.dead_of_hasExtension`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement.exists_safe_degree`
