# Actual leaf pruning extracts singly attached ordinary hair trees

## Abstract

Actual leaf pruning extracts singly attached ordinary hair trees

**Theorem 1.1 (A rotor step keeps its actual owner orbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.vertexOf_next`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.vertexOf_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite or infinite flag carrier, applying its cubic vertex rotor leaves the actual owner-orbit vertex unchanged. This existing orbit helper is exposed for the connected fixed-genus source-quotient comparison, where actual incidence reachability must be transferred through the local AS and IHX tables.

**Theorem 1.2 (Owner equality is exactly one of the three literal rotor positions).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.vertexOf_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.vertexOf_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two flags have the same actual owner orbit exactly when the second is the first flag, its next rotor flag, or its second rotor flag. The statement includes univalent fixed rotor flags. The connected source-grade comparison consumes this existing helper to transfer paths without adding an assumed graph isomorphism.

**Definition 1.3 (Chronological deletion with literal residual flag degree).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.LeafPruning`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.LeafPruning` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A LeafPruning of a finite cyclic FlagGraph assigns distinct chronological ranks to removed rotor orbits and the terminal rank to retained orbits. Each removal has at most one literal flag whose mate still belongs to a vertex of the same or a later rank; both flags of any loop are therefore counted. All numbered anchor vertices are protected, and every terminal nonanchor vertex has at least two remaining flags. The source incidence graph retains actual rotor orbits and individual edge flags separately, preserving loops and parallel edges. Source stability means an actual incidence cycle or two distinct protected anchor vertices. No forest, boundary, binary-tree shape or placement property is part of the pruning input.

**Definition 1.4 (Extracting the literal open tree and its external parent).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.extractComponentHair`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.extractComponentHair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a connected stable source, deletion ranks refine to leaf-deletion ranks on the actual incidence graph. The earliest vertex of a cycle or of a simple path with retained endpoints cannot be deleted. Consequently the retained incidence core is connected and contains an edge. Every deleted component is acyclic and has exactly one boundary adjacency: a path between two boundaries would force its earliest vertex to have two distinct later neighbors. The expanded deleted component contains one exterior mate flag at its retained parent; removing this degree-one flag leaves precisely the incidence graph of the extracted OpenHair. Its flag set consists exactly of original flags whose removed owner vertex lies in the component. Rotor and labels are inherited literally, and only the root pairing is changed to a fixed point. The connected core supplies another retained flag at the exterior owner, proving that the disjoint ambient parent is trivalent. Anchor protection makes every univalent component flag ordinary. The resulting PrunedComponentHair records the tree proof, actual OpenHairPlacement, exact source flag range, unique boundary and equality with the original rotor-fixed component leaf count.

**Theorem 1.5 (A genuinely pruned branching component vanishes).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.pruned_branching_component_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.pruned_branching_component_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a finite connected cyclic flag graph with an actual cycle or two distinct protected anchor vertices, and let P be a genuine terminal leaf-pruning chronology. If any deleted incidence component has at least two original rotor-fixed flags at its removed owner vertices, then classOf G is zero in the actual rational AS, IHX and ordinary CL quotient. The proof constructs the actual open component and its trivalent placement, preserves its exact number of ordinary leaves, and invokes actual_branching_hair_vanishes through the literal HairTree representation. Terminal-cherry extraction gives an actual cherry in the full graph; its vanishing uses IHX, ordinary CL, an explicit flag isomorphism and two vertex AS relations. No induction on a degree cutoff enters this reduction.

For a connected source with fixed original Euler genus g and every ordinary-color and anchor-label population, FlagEulerBridge turns positive genus into an actual incidence cycle. LeafPruningExistence supplies a terminal chronology P without a pruning assumption. ConnectedFlagGrade then reflects the vanishing back to the quotient with that exact connected genus-and-population grade. Thus every component deleted by such a P with at least two ordinary leaves makes the original finite-flag source class zero, under positive genus or two distinct protected anchors. The bare topological circle has no attached tree and contributes no case to this implication. Core uniqueness, the global skeleton and insertion normal form, and the full four-loop theorem are separate statements.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.LeafPruning`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.extractComponentHair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.pruned_branching_component_vanishes`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.vertexOf_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.vertexOf_next`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks](LeafPruningRanks.md)
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/OpenHairRepresentation](OpenHairRepresentation.md)
