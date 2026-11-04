# Finite set-form Menger certificates

## Abstract

Finite vertex separators attain disjoint path certificates, with sharp weak duality for arbitrary walks.

**Definition 1.1 (Separation by full walk support).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall A \in \operatorname{Finset}\left(V\right),\; \forall B \in \operatorname{Finset}\left(V\right),\; \forall X \in \operatorname{Finset}\left(V\right),\; \operatorname{Separates}\left(G, A, B, X\right) \Leftrightarrow \left(\forall a \in V,\; a \in A \Rightarrow \left(\forall b \in V,\; b \in B \Rightarrow \left(\forall p \in \operatorname{Walk}\left(G, a, b\right),\; \exists x \in V,\; x \in X \land x \in \operatorname{support}\left(p\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/MengerCertificates.Separates` (`✓ std3`).

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and set-form Menger: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

Separates(G,A,B,X) means that every G-walk starting in A and ending in B has a vertex in X in its support. Support includes both endpoints. There is no restriction that X avoid A or B.

**Theorem 1.2 (An attained certificate and universal walk weak duality).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall A \in \operatorname{Finset}\left(V\right),\; \forall B \in \operatorname{Finset}\left(V\right),\; \left(\exists X \in \operatorname{Finset}\left(V\right),\; \operatorname{Separates}\left(G, A, B, X\right) \land \left(\exists a \in \operatorname{Fin}\left(\operatorname{card}\left(X\right)\right) \to V,\; \exists b \in \operatorname{Fin}\left(\operatorname{card}\left(X\right)\right) \to V,\; \exists p \in \operatorname{WalkFamily}\left(G, a, b\right),\; \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(X\right)\right),\; \operatorname{a}\left(i\right) \in A \land \left(\operatorname{b}\left(i\right) \in B \land \operatorname{IsPath}\left(\operatorname{p}\left(i\right)\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(X\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{card}\left(X\right)\right),\; i \ne j \Rightarrow \left(\forall x \in V,\; x \in \operatorname{support}\left(\operatorname{p}\left(i\right)\right) \Rightarrow \left(\neg x \in \operatorname{support}\left(\operatorname{p}\left(j\right)\right)\right)\right)\right)\right)\right) \land \left(\forall Y \in \operatorname{Finset}\left(V\right),\; \operatorname{Separates}\left(G, A, B, Y\right) \Rightarrow \left(\forall m \in \mathrm{Nat},\; \forall a \in \operatorname{Fin}\left(m\right) \to V,\; \forall b \in \operatorname{Fin}\left(m\right) \to V,\; \forall p \in \operatorname{WalkFamily}\left(G, a, b\right),\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{a}\left(i\right) \in A\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{b}\left(i\right) \in B\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; i \ne j \Rightarrow \left(\forall x \in V,\; x \in \operatorname{support}\left(\operatorname{p}\left(i\right)\right) \Rightarrow \left(\neg x \in \operatorname{support}\left(\operatorname{p}\left(j\right)\right)\right)\right)\right) \Rightarrow m \le \operatorname{card}\left(Y\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MengerCertificates.exists_separator_paths_and_weak_duality` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic, finite chordal elimination and set-form Menger: Lean sources*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

For every vertex type V in any universe with Finite(V), every simple undirected graph G on V, and arbitrary finite vertex sets A and B, there is a finite separator X and an indexed family of exactly card(X) paths with initial vertices in A, final vertices in B, and pairwise disjoint full vertex supports. The same G, A and B satisfy the universal second clause: every finite separator Y bounds the size m of every pairwise vertex-disjoint family of A-to-B walks. The latter walks need not be paths.

In the displayed formula, Fin(n) is the index type with n elements, a and b are functions from this index type to V, and WalkFamily(G,a,b) is the dependent product of G.Walk(a(i),b(i)) over that index type. The product contains actual walks, including nil walks. IsPath is required only for the attained certificate. Disjointness quantifies over every vertex of each support, including endpoints.

Empty V, empty terminal sets, overlapping A and B, endpoint separators and zero-length paths remain in scope. In particular, the edge-free induction base uses nil paths at A intersect B. There is no connectedness, terminal-disjointness, distinct-terminal, nonadjacency or positive-length assumption. Directed, infinite-vertex, edge-disjoint and special two-terminal variants are outside this statement.

The proof is received from Juan Pablo Traverso Gianini's jtraverso/menger-hamiltonian at immutable commit 35c5f684f9bfbd244bd0999ce725623ab571adb6. The source attributes its edge-induction proof to the second proof of Diestel, Graph Theory, Theorem 3.3.1 (Boehme, Goering, Harant). The private induction preserves the stronger terminal-clean Fam invariant because the splice consumes it; only the public output forgets those extra cleanliness clauses. Weak duality chooses a separator vertex on each walk and proves that disjointness makes this choice injective. This is known mathematics with source proof attribution.

The source copyright and full Apache license are retained in the Lean source and docs/reports/licenses/menger-hamiltonian-LICENSE.txt. Retire this port when this repository's own pinned Mathlib supplies an equivalent entire finite set-form certificate and arbitrary-walk duality, after lawful migration of all consumers to direct applications.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MengerCertificates.Separates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MengerCertificates.exists_separator_paths_and_weak_duality`
