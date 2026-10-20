# Nonradical lines preserve the full orthogonality graph

## Abstract

A retraction onto lines and pairwise totally isotropic subspaces in every binary dimension.

**Definition 1.1 (The retained vertices).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.Retained`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.Retained` (`✓ std3`).

*Citation.* Public binary-subspace-orthogonality research workspace; note without individual byline (2026). *Retaining only lines and totally isotropic subspaces*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/notes/nonradical-line-retraction.md>.

*Commentary.*

Let F=ZMod 2, V(n)=Fin n -> F, and B be the existing standard coordinate pairing. Vertex(n) is the existing subtype of all nonzero submodules of V(n), including top. Retained(n,U) means finrank F U=1 or B(u,v)=0 for every u,v in U. The isotropic condition is pairwise; vanishing of B(u,u) alone is insufficient. A line can satisfy both branches.

**Definition 1.2 (The induced graph).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.retainedGraph`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.retainedGraph` (`✓ std3`).

*Citation.* Public binary-subspace-orthogonality research workspace; note without individual byline (2026). *Retaining only lines and totally isotropic subspaces*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/notes/nonradical-line-retraction.md>.

*Commentary.*

Write G(n) for NikandishClique.orthogonalityGraph n and S(n) for retainedGraph n. S(n) is G(n) induced on the actual subtype T(n) of retained vertices. Both graphs have distinct orthogonal endpoints as their adjacency relation. Write val for the inclusion T(n) -> Vertex(n), and space(U) for its submodule.

**Theorem 1.3 (The complete contained retraction).**

$$\forall n \in Nat,\; \exists r \in GraphHom(G(n),S(n)),\; (\forall U \in T(n),\; apply(r,val(U)) = U) \land ((\forall U \in Vertex(n),\; space(apply(r,U)) \subseteq space(U)) \land (\forall U \in Vertex(n),\; (val(apply(r,U)) \ne U) \Rightarrow ((dim(space(apply(r,U))) = 1) \land ((\neg space(apply(r,U)) \subseteq orthogonal(B(n),space(U))) \land (\exists v \in V(n),\; (v \in space(U)) \land ((v \ne 0) \land ((space(apply(r,U)) = span(F,v)) \land (\exists w \in V(n),\; (w \in space(U)) \land (pair(B(n),v,w) \ne 0)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.result` (`✓ std3`). ∎

*Citation.* Public binary-subspace-orthogonality research workspace; note without individual byline (2026). *Retaining only lines and totally isotropic subspaces*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/notes/nonradical-line-retraction.md>.

*Commentary.*

For every natural dimension n there is a graph homomorphism r:G(n)->S(n) fixing every vertex of T(n), with space(r(U)) contained in space(U). Whenever val(r(U)) differs from U, its image has dimension one and is not contained in the right orthogonal of space(U). More precisely, its image is F span v for a nonzero v in U and some w in U has B(v,w) nonzero. The formula abbreviates finrank F by dim and uses B(n) on V(n).

A vertex outside T(n) is not totally isotropic, so two vectors v,w in it have B(v,w) nonzero. The span of v is a nonzero line contained in that vertex. Symmetry converts B(v,w) nonzero to failure of membership in the right orthogonal. Choose such a line for each vertex outside T(n), and keep the vertices of T(n) fixed. No condition on B(v,v) is imposed.

Containment sends orthogonal sources to orthogonal images. If an edge's images were equal and either endpoint moved, their common image would lie in the other endpoint and hence in the moved source's orthogonal, contradicting nonradicality. If neither endpoint moved, equality would contradict the original edge's distinctness. Thus r preserves actual edges.

For any palette type alpha, a Coloring alpha on S(n) pulls back by Coloring.comap r. A Coloring alpha on G(n) restricts by Coloring.comap of (SimpleGraph.Embedding.induce).toHom. Hence Nonempty (G(n).Coloring alpha) is equivalent to Nonempty (S(n).Coloring alpha), including empty palettes. Applying chromaticNumber_mono_of_hom in both directions and antisymmetry gives equality of their Nat-infinity chromatic numbers. Colorable.of_hom is the corresponding consequence for palettes Fin k; it is not the arbitrary-palette predicate.

At n=0 the original carrier is empty. At n=1 every vertex is the one-dimensional whole space and is retained. Top is included when nonzero (n>=1). In dimension two the vector (1,1) is self-isotropic but pairs nontrivially with (1,0), so its isotropic line is a permitted nonradical image of top. No finite cutoff or exact finite coloring number is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.Retained`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.result`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction.retainedGraph`
- Dependency: [D5/S3/Combinatorics/Orthogonality/NikandishClique](NikandishClique.md)
