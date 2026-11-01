# Exact source labels and the unbounded-order reduction

## Abstract

The source graph has the published 33 labels and 36 edges; its base evaluation is an explicit premise of the family reduction.

**Definition 1.1 (The authenticated finite edge data).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.sourceEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.sourceEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 36 unordered source edges are independently encoded from Alikhani and Griswold, On the Integer Domination Root Conjecture, arXiv:2608.00109v1. The four-cycle has vertices 0,1,2,3. The eight attached components occupy labels 4 through 32. The explicit edge list determines the graph; the source branch description is not used as a certificate.

**Definition 1.2 (The actual source graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.sourceGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.sourceGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adjacency holds when either orientation belongs to sourceEdges. The graph is loopless by kernel finite decision and undirected by symmetry of the disjunction. Vertex 5 has sole neighbor 4. Connectedness is proved using a parent for every nonzero label, with each parent strictly smaller and joined by an actual source edge. Strong induction on the label gives a path to vertex 0.

**Theorem 1.3 (The exact original event conditional on the base root).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.result_of_base_root`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.result_of_base_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume precisely that evaluation(sourceGraph,minus four) equals zero. For every natural N choose r=N+1 copies attached at the actual support 4, retaining its actual internal leaf 5. The weighted support theorem gives eight times zero to the positive power r, hence zero. Connectedness follows from the copy paths. The vertex count is 33r+2, strictly greater than N. Fintype.equivFin relabels the actual replicated vertex type onto Fin n. The graph isomorphism transports domination bijectively and the finset map preserves cardinality, hence every weight. This yields the full existential event on Fin n, with no requirement that dominating subsets be connected.

The base premise is discharged by the exact restriction/reassembly identity and finite component calculations in MinusFourReassembly and MinusFourBaseStates. The published report alone is not used as a proof. The question in Section 4 item 3 asks for an infinite family. The strictly increasing orders supply pairwise nonisomorphic graphs. The published base itself earns no new-resolution credit. No minimum-order, other-integer-root, degree-bound or cyclomatic-number assertion follows.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.result_of_base_root`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.sourceEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.sourceGraph`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/MinusFourReplication](MinusFourReplication.md)
