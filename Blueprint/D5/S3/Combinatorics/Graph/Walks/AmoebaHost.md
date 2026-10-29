# Finite Buffered Hosts for Ordinary Amoebas

## Abstract

A finite layered supertree preserves every initial tree, realizes all arm paths simultaneously for every copy, and is confining under total-edge minimization.

Host, extensionGraph and HasExtension have the meanings given in AmoebaConfinement. The source target is Gurvich–Krnc–Vyalyi Conjecture 1, arXiv:2401.07484v1/v2 and DOI 10.1007/s00025-025-02421-6. The construction supplies a finite host for every initial finite tree and controls all copies and all multiplicity placements. All nonnegative extension lengths and multiplicities are retained. The final assertion uses the finite source convention; it makes no claim about infinite hosts with cardinal edge minimization.

sprout(P,p) has vertex type V disjoint union L. It retains P on V and makes each a in L a new leaf adjacent only to p(a). A Layered(T,M,q,N) consists of a finite tree S, a core copy of T, and a natural-valued level function. The level is zero exactly on the core and at most N everywhere. Core degrees are at least M, positive levels below N have degree q, and level N has degree one. Adjacent levels differ by at most one. The construction starts with M new leaves at each core vertex, then repeatedly attaches q−1 new leaves to every outer leaf. Counting old edges and new leaves proves that each stage is still a finite tree.

**Theorem 1.1 (Every copy remains close to the core).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; (\mathrm{IsTree}\left(H\right)) \Rightarrow (\forall T \in \mathrm{Host},\; \forall M \in \mathrm{Nat},\; \forall q \in \mathrm{Nat},\; \forall N \in \mathrm{Nat},\; \forall A \in \mathrm{Layered}\left(T, M, q, N\right),\; (1 \le q) \Rightarrow ((q < \mathrm{maxDegree}\left(H\right)) \Rightarrow (\forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(\mathrm{host}\left(A\right)\right)\right),\; \exists v \in V,\; (\mathrm{level}\left(A, \mathrm{c}\left(v\right)\right) = 0) \land (\forall w \in V,\; \mathrm{level}\left(A, \mathrm{c}\left(w\right)\right) < \mathrm{card}\left(V\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.copy_level_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

Choose a maximum-degree vertex in H. Its image cannot lie outside the core because every outside degree is at most q. For each other vertex, the unique H-path from that vertex maps to an actual host path. Its length is less than the order of H. The level changes by at most one per edge, so the stated bound holds for every vertex of every copy.

**Theorem 1.2 (All-copy degree budgets in one finite supertree).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; (\mathrm{IsTree}\left(H\right)) \Rightarrow (\forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; (\mathrm{sum}\left(m\right) + 2 < \mathrm{maxDegree}\left(H\right)) \Rightarrow (\forall T \in \mathrm{Host},\; \exists q \in \mathrm{Nat},\; \exists M \in \mathrm{Nat},\; \exists A \in \mathrm{Layered}\left(T, M, q, \mathrm{card}\left(V\right) + l + 1\right),\; (2 \le q) \land ((q \le \mathrm{sum}\left(m\right) + 2) \land ((q < \mathrm{maxDegree}\left(H\right)) \land ((2 \le M) \land ((\forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(\mathrm{host}\left(A\right)\right)\right),\; \forall v \in V,\; \mathrm{level}\left(A, \mathrm{c}\left(v\right)\right) < \mathrm{card}\left(V\right)) \land ((\forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(\mathrm{host}\left(A\right)\right)\right),\; \forall v \in V,\; \mathrm{degree}\left(H, v\right) + \mathrm{m}\left(v\right) \le \mathrm{degree}\left(\mathrm{graph}\left(\mathrm{host}\left(A\right)\right), \mathrm{c}\left(v\right)\right)) \land (\forall x \in \mathrm{Vertex}\left(\mathrm{host}\left(A\right)\right),\; (\mathrm{level}\left(A, x\right) < \mathrm{card}\left(V\right) + l + 1) \Rightarrow (2 \le \mathrm{degree}\left(\mathrm{graph}\left(\mathrm{host}\left(A\right)\right), x\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.exists_buffered_host` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

Put k equal to the sum of m. Select q between 2 and k+2 avoiding every interval from degree(v) to degree(v)+m(v). Use core degree budget M equal to maximum degree plus k plus two, and outer depth equal to the order of H plus l plus one. Every copy lies below the order of H in level. At a core vertex the M budget supplies its degree demand. At a branch vertex its degree is q; containment gives degree(v) at most q, and the safe-degree choice then supplies degree(v)+m(v). Every vertex below the outer level has degree at least two. The core copy explicitly preserves the arbitrary initial T; no assumption that an extension is already present is used.

**Theorem 1.3 (Jointly fresh leaf attachment).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall W \in \mathrm{Type},\; [\mathrm{Fintype}\left(W\right)] \forall L \in \mathrm{Type},\; [\mathrm{Fintype}\left(L\right)] \forall P \in \mathrm{SimpleGraph}\left(V\right),\; \forall G \in \mathrm{SimpleGraph}\left(W\right),\; (\mathrm{IsTree}\left(P\right)) \Rightarrow ((\mathrm{IsTree}\left(G\right)) \Rightarrow (\forall c \in \mathrm{Copy}\left(P, G\right),\; \forall p \in L \to V,\; (\forall v \in V,\; \mathrm{degree}\left(P, v\right) + \mathrm{card}\left(\mathrm{parentFiber}\left(p, v\right)\right) \le \mathrm{degree}\left(G, \mathrm{c}\left(v\right)\right)) \Rightarrow (\exists e \in \mathrm{Copy}\left(\mathrm{sprout}\left(P, p\right), G\right),\; \forall v \in V,\; \mathrm{e}\left(\mathrm{inl}\left(v\right)\right) = \mathrm{c}\left(v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.sprout_copy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

The image of a connected tree inside a tree is induced: its paths are unique, so an extra image edge would form a cycle. A vertex outside that image cannot be adjacent to two distinct image vertices for the same reason. At each parent, removing its image neighbors leaves enough neighbors for the prescribed new leaves. Choose an injection on each parent fiber. Distinct fibers cannot collide by the unique-attachment property, so all chosen leaves are fresh and jointly distinct.

**Theorem 1.4 (The simultaneous first arm edges).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; (\mathrm{IsTree}\left(H\right)) \Rightarrow (\forall m \in V \to \mathrm{Nat},\; \forall G \in \mathrm{Host},\; \forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(G\right)\right),\; (\forall v \in V,\; \mathrm{degree}\left(H, v\right) + \mathrm{m}\left(v\right) \le \mathrm{degree}\left(\mathrm{graph}\left(G\right), \mathrm{c}\left(v\right)\right)) \Rightarrow (\mathrm{HasExtension}\left(m, 1, c\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.hasExtension_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

Apply the joint leaf-attachment theorem to the root-occurrence type consisting of pairs (v,a) with a below m(v). Its parent fiber over v has exactly m(v) elements. Forgetting the unique Fin(1) coordinate identifies these leaves with the explicit length-one extension graph. Thus every first arm edge is realized simultaneously. These edges initialize the paths in the following continuation lemma.

**Theorem 1.5 (Simultaneous arms of every finite length).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; (\mathrm{IsTree}\left(H\right)) \Rightarrow (\forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall G \in \mathrm{Host},\; \forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(G\right)\right),\; \forall level \in \mathrm{Vertex}\left(G\right) \to \mathrm{Nat},\; \forall N \in \mathrm{Nat},\; (\forall x \in \mathrm{Vertex}\left(G\right),\; \forall y \in \mathrm{Vertex}\left(G\right),\; (\mathrm{Adj}\left(\mathrm{graph}\left(G\right), x, y\right)) \Rightarrow (\mathrm{level}\left(x\right) \le \mathrm{level}\left(y\right) + 1)) \Rightarrow ((\forall x \in \mathrm{Vertex}\left(G\right),\; (\mathrm{level}\left(x\right) < N) \Rightarrow (2 \le \mathrm{degree}\left(\mathrm{graph}\left(G\right), x\right))) \Rightarrow ((\forall v \in V,\; \mathrm{degree}\left(H, v\right) + \mathrm{m}\left(v\right) \le \mathrm{degree}\left(\mathrm{graph}\left(G\right), \mathrm{c}\left(v\right)\right)) \Rightarrow ((\forall v \in V,\; \mathrm{level}\left(\mathrm{c}\left(v\right)\right) + l < N) \Rightarrow (\mathrm{HasExtension}\left(m, l, c\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.hasExtension_of_buffer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

For zero length the extension is the existing copy. For positive length, start with the jointly fresh first edges. Continue each arm by choosing a neighbor other than its predecessor. The level buffer keeps every endpoint below the outer leaves. Acyclicity makes every such continuation a path. A path whose first edge leaves the connected copy cannot return to it: a return would give two distinct paths between copy vertices. Likewise, two off-copy arm tails can meet only if their roots and first edges agree. The first-edge injection then identifies their root occurrences. Path simplicity identifies their position indices. The resulting injective homomorphism realizes the entire explicit extension graph.

**Theorem 1.6 (The full ordinary-amoeba total-confinement assertion).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; (\mathrm{IsTree}\left(H\right)) \Rightarrow (\forall m \in V \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; (\mathrm{sum}\left(m\right) + 2 < \mathrm{maxDegree}\left(H\right)) \Rightarrow (\forall T \in \mathrm{Host},\; (\mathrm{Nonempty}\left(\mathrm{Copy}\left(H, \mathrm{graph}\left(T\right)\right)\right)) \Rightarrow (\exists S \in \mathrm{Host},\; (\mathrm{Nonempty}\left(\mathrm{Copy}\left(\mathrm{graph}\left(T\right), \mathrm{graph}\left(S\right)\right)\right)) \land ((\mathrm{Nonempty}\left(\mathrm{Copy}\left(H, \mathrm{graph}\left(S\right)\right)\right)) \land (\forall c \in \mathrm{Copy}\left(H, \mathrm{graph}\left(S\right)\right),\; \mathrm{Dead}\left(m, l, c\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement` (`✓ std3`). ∎

*Resolves.* `Problems/gurvich-krnc-vyalyi-conjecture-1-total-amoeba-confinement` (proved) by `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gurvich-krnc-vyalyi-conjecture-1-total-amoeba-confinement","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Gurvich; Matjaž Krnc; Mikhail Vyalyi (2025). *Growing Trees and Amoebas’ Replications*. DOI: [10.1007/s00025-025-02421-6](https://doi.org/10.1007/s00025-025-02421-6). URL: <https://arxiv.org/abs/2401.07484>.

*Commentary.*

For any finite tree H and nonnegative multiplicities, assume its maximum degree exceeds the multiplicity sum plus two. Given an arbitrary finite initial T containing H, use its buffered layered host S. Every copy has the root degree budgets and the full path-length margin, so the simultaneous extension lemma applies to every copy, with its own transported multiplicities. The minimum-total-edge bridge makes every one of these copies dead for every minimizing growth. Composing the preserved core embedding with the initial copy also proves that S admits a copy. Thus S is confining and contains the arbitrary T.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.copy_level_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.exists_buffered_host`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.hasExtension_of_buffer`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.hasExtension_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.sprout_copy`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AmoebaHost.total_confinement`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement](AmoebaConfinement.md)
