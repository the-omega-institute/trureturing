# Actual acyclic hair components admit binary-tree models

## Abstract

Actual acyclic hair components admit binary-tree models

**Definition 1.1 (Incidence graph with literal edge flags).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.incidence`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite OpenHair T, vertices are actual orbits of its cubic rotor. The incidence graph has the disjoint vertex types VertexOrbit and Flag. Each flag is joined to its own rotor orbit, and distinct paired flags are joined to one another. The root's artificial fixed edge pairing adds no loop. Actual original loops become triangles, and parallel original edges have separate flag vertices, so this encoding retains the distinctions needed by the acyclicity hypothesis.

**Theorem 1.2 (A literal colored binary-tree representation).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.exists_hairTree_model`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.exists_hairTree_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite OpenHair whose actual incidence graph is connected and acyclic, and whose rotor-fixed flags all have ordinary red or blue labels, admits a finite HairTree Color and an OpenHairIso from that tree's model to T. The isomorphism is a bijection of literal flags preserving the root, rotor, edge pairing and every label. Starting at the root flag, each outgoing branch extends an incidence path by three fresh steps. A path's length is less than the finite incidence vertex count, which bounds the recursive unfolding. Rotor and color preservation make its incidence map locally injective; acyclicity prevents path folding and gives global injectivity. Connectedness supplies surjectivity through closure under rotor and edge pairing.

**Theorem 1.3 (The model has exactly its ordinary tree leaves).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.model_leafCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.model_leafCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OpenHair.leafCount counts actual rotor-fixed flags. A leaf model contributes exactly one such flag, while a binary node contributes none and retains exactly its two children's fixed flags. Hence t.model.leafCount equals t.leafCount. A literal OpenHairIso also preserves this count, so the representation has exactly the original component's number of leaves. OrdinaryLeaves ensures that every leaf counted in the vanishing theorem carries an ordinary color rather than an anchor.

**Definition 1.4 (Geometric component data and an external trivalent parent).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.OpenHairPlacement`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.OpenHairPlacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An OpenHairPlacement G T is an injective inclusion of T's actual flags into G, preserving the rotor, labels and every nonroot pairing. The root is paired to flag zero of a genuine trivalent ambient parent, all three of whose flags lie outside the component image. This data contains no binary-tree shape and assumes no recursive HairPlacement. Composing the constructed flag isomorphism with this inclusion gives the existing HairPlacement with the same parent and root pairing.

**Theorem 1.5 (Vanishing of a placed actual acyclic hair component).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.actual_branching_hair_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.actual_branching_hair_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any finite actual cyclic flag graph and let T be an actual OpenHair with connected acyclic incidence graph, only ordinary colored leaves, and at least two such leaves. Given an OpenHairPlacement G T with a disjoint external trivalent parent, classOf G is zero in the actual rational AS, IHX and ordinary CL quotient. The literal representation and exact leaf count give a branching HairPlacement, from which the existing terminal-cherry theorem and actual local relation proof yield vanishing. The ambient graph may have arbitrary numbered anchors or cycles outside the included component. This theorem takes the stated geometric component data as inputs; identifying a component of a separately defined deleted-core graph with these inputs remains a separate obligation, as do the global core presentation and four-loop vanishing.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.OpenHairPlacement`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.actual_branching_hair_vanishes`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.exists_hairTree_model`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.incidence`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation.model_leafCount`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/HairPlacement](HairPlacement.md)
