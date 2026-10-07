# Directed forest reconstruction

## Abstract

Generator-labelled arc elimination solves all nonroot coordinates and leaves one ordered residual at each actual powered component root.

**Definition 1.1 (Arc).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.Arc`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.Arc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A directed variable is a pair consisting of a generator index in Fin m and a source coordinate in I. Oppositely directed arcs remain separate variables, including when their endpoints coincide in reverse order.

**Definition 1.2 (incident).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.incident`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.incident` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arc is incident to its source and to the image of its source under its labelled permutation. A loop has the same two endpoints and is excluded from leaf elimination.

**Definition 1.3 (vertex).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a group S, permutations tau and arbitrary component automorphisms alpha, the vertex word is the generator-ordered product of the inverse outgoing arc variable times the incoming arc variable transformed by its own component automorphism. No relation between opposite component automorphisms is assumed.

**Theorem 1.4 (actual vertex).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_vertex`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_vertex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the actual factor coordinate law, with tau(j) equal to sigma(j) to the q power and alpha given by the q-step corrected component, the directed vertex word equals the corrected q-powered commutator coordinate. This is the exact equation (47) word.

**Theorem 1.5 (vertex update bijective).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex_update_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex_update_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix every arc except one nonloop arc incident to a vertex. As the remaining arc variable ranges over S, the vertex word is bijective. At the source it occurs inversely, and at the target its own automorphism applies; the surrounding products retain their order.

**Definition 1.6 (LeafOrder).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.LeafOrder`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.LeafOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every listed pair consists of a vertex and an incident nonloop arc. The pairwise condition says a later selected arc is not incident to an earlier listed vertex, so subsequent updates preserve equations already solved.

**Definition 1.7 (solve).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.solve`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.solve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonloop arc incident to the specified vertex, choose the unique replacement value solving that vertex target by the update bijection. On other pairs the definition keeps the current value.

**Definition 1.8 (eliminate).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Process a leaf order recursively. At each listed pair, update exactly its selected arc to the value solving its target vertex. All other arc variables pass to the next step unchanged.

**Theorem 1.9 (eliminate unused).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unused`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unused` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arc that is never selected by the elimination list retains its original value. This includes all unused labelled arcs.

**Theorem 1.10 (eliminate loop).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_loop`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid leaf order, every loop arc retains its original value because selected arcs are nonloops.

**Theorem 1.11 (eliminate solves).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_solves`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_solves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid leaf order, the final eliminated assignment solves every listed vertex equation. The pairwise nonincidence condition ensures later replacements do not alter earlier equations.

**Theorem 1.12 (eliminate unique).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unique`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid leaf order, any assignment agreeing with the initial assignment on unused arcs and solving all listed vertices equals the eliminated assignment. Induction uses uniqueness of each incident-arc replacement.

**Theorem 1.13 (reconstruction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid leaf order and any initial assignment, an assignment preserving every unused arc and solving every vertex exists exactly when the eliminated assignment satisfies every vertex not listed. Both directions use the same initial unused-arc data.

**Theorem 1.14 (exists actual leafOrder).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.exists_actual_leafOrder`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.exists_actual_leafOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be finite and r select one root per actual q-powered component: r(v) is reachable from v and r is constant on reachability classes. Construct an acyclic spanning subgraph with the same reachability, together with a valid leaf order listing precisely vertices v different from r(v). Every selected variable is an actual generator-labelled arc belonging to the spanning forest. Sorting by decreasing distance permits mixed edge orientations.

**Theorem 1.15 (actual forest reconstruction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_forest_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_forest_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate type I, a group S, actual k, sigma and beta satisfying the coordinate law, a fixed correction tuple y and a root map r reachable from and constant on each actual q-powered component, there exists a leaf order listing exactly the nonroots. For every tuple target kappa and every initial arc assignment a, a corrected q-powered solution preserving all unused arcs exists if and only if the eliminated assignment solves the equation at each root v equal to r(v). Thus there is one exact ordered residual per powered component, including isolated vertices; original transitivity is not required.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Lemma 10.3 and equations (45)-(50), printed pages 228-231. The scalar PRODUCT premise is the input of Part II, Theorem 1.2, equivalent to Part I, Theorem 1.10; Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. These are adaptations and proofs of conditional consequences of published mathematics, with no originality claim. Uniform scalar existence, genuine type-II reconstruction, mixed representative bounds, uniform width, restricted Burnside bounds and unconditional strong completeness remain unproved.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.Arc`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.LeafOrder`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_forest_reconstruction`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.actual_vertex`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_loop`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_solves`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unique`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.eliminate_unused`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.exists_actual_leafOrder`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.incident`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.reconstruction`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.solve`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Equation47Forest.vertex_update_bijective`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TransitiveCoordinates](TransitiveCoordinates.md)
