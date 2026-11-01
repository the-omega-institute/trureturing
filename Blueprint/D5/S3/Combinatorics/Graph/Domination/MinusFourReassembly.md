# Restriction, root states, and the connected family

## Abstract

An exact restriction and union correspondence connects the actual source graph to the eight-component weighted calculation.

**Theorem 1.1 (The exact weighted reassembly identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.source_reassembly`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.source_reassembly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source vertex coordinates are the disjoint sum of Fin 4 and the eight dependent component types. The map sends a core coordinate to its own label and a component coordinate to branchStart(i)+v. Its bijectivity is checked on the actual 33 labels. Assembly takes the disjoint union of the core set and the eight local sets, then maps through this equivalence. Restriction and assembly are inverse, and the cardinality is the core cardinality plus the sum of the component cardinalities. No vertex or subset is lost or duplicated. Every component root has its actual local leaf at coordinate one. Global domination of this leaf forces its root or leaf to be selected and hence forces internal domination of the root. Every other component vertex has only internal neighbors. The exact core-neighbor characterization is the four-cycle adjacency together with the published root incidences. Thus an assembled set dominates exactly when all eight local sets internally dominate and the selected core and roots cover the core. Partitioning each local family by its root membership gives the typed configuration family. The map from these configurations to domSets(sourceGraph) is injective by restriction and surjective by the domination characterization. The equivalence transports the sum of cardinality weights. Fintype.prod_sum separates the independent component choices and their sums are exactly the eight messages. The resulting expression is stateEvaluation.

**Theorem 1.2 (The complete unbounded-order ordinary-domination event).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N there exist n greater than N and a connected finite simple undirected graph G on Fin n whose sum of minus four raised to the cardinality of S over all ordinary dominating subsets S is zero. The exact reassembly identity supplies the premise of the finite-state reduction. Its local messages and core cancellation give the base value zero. The existing support-replication construction uses N+1 copies of the actual 33-vertex base, attaches their actual support 4 to one hub, and adds the hub pendant. Its order is 33(N+1)+2. Since leaf 5 remains internal in each copy, partial domination outside support 4 equals full domination. The weighted replication value is eight times the positive power N+1 of the base value. Copy paths through support 4 prove connectedness, and graph isomorphism transport gives the exact Fin n statement while preserving domination, cardinality and weights.

The source question is Section 4 item 3 of Alikhani and Griswold, arXiv:2608.00109v1. The source graph and its reported finite root are prior results, and the source graph is encoded independently from its explicit edge list. This argument addresses the connected unbounded-family event. It does not require a dominating subset to be connected, or impose a fixed degree or cyclomatic number. It asserts no result about the smallest possible order or about other integer roots. The library search supplies existing domination, leaf, transport, replication and finite-sum interfaces; the reassembly and family application are repository derivations without a worldwide priority claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.source_reassembly`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates](MinusFourBaseStates.md)
