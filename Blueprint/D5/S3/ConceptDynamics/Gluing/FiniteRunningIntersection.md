# Finite running-intersection computation

## Abstract

Finite separator computation and reconstruction on a general running-intersection tree.

The input consists of finite node, variable and output types with their actual enumerations and equality decisions, a decidable SimpleGraph T, decidable scopes S n, and finite tables L n of complete assignments on S n. T is a tree and the nodes containing each variable form a preconnected induced graph. No equality of the original neighboring projection images is required. Empty scopes, empty separators, empty relations and a singleton support tree are allowed.

**Theorem 1.1 (Finite messages refine the semantic recurrence).**

$$(\forall d: FiniteJoinData, (\forall e: \operatorname{Dart}\left(\operatorname{graph}\left(d\right)\right), (\forall a: \operatorname{Assignments}\left(\operatorname{output}\left(d\right), \operatorname{sep}\left(d, e\right)\right), a \in \operatorname{messageTable}\left(d, e\right) \iff a \in \operatorname{separatorMessages}\left(d, e\right)) \land \operatorname{card}\left(\operatorname{messageTable}\left(d, e\right)\right) \le \operatorname{power}\left(\operatorname{card}\left(\operatorname{output}\left(d\right)\right), \operatorname{card}\left(\operatorname{sep}\left(d, e\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.message_table_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FiniteJoinData abbreviates the complete telescope of message_table_spec: Node, Var and O with their finite enumerations and equality decisions, T with decidable adjacency, S with decidable membership, L, and the proof that T is a tree. sep d e is S e.snd intersect S e.fst; assignments are functions on exactly this separator with values in O. The semantic message is separatorMessages for the set underlying each input table. messageTable filters each local row against every adjacent nonparent message and then projects surviving rows to the separator. The genuine deleted-edge child component strictly decreases by the termination argument of separatorMessages, also giving termination for every finite degree. The actual output table is a subset of the original assignment carrier, including the single empty assignment when the separator is empty.

**Theorem 1.2 (A finite occurrence decoder reconstructs the certificate).**

$$(\forall d: DecodeData, (\forall a: \operatorname{RowFamily}\left(d\right), \operatorname{Valid}\left(d, a\right) \to (\forall n: \operatorname{Nodes}\left(d\right), \operatorname{restrict}\left(\operatorname{decode}\left(d, a\right), \operatorname{scope}\left(d, n\right)\right) = \operatorname{row}\left(a, n\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.decode_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DecodeData abbreviates the complete telescope of decode_spec, including the finite native carriers, graph, scopes, input tables, tree and running intersection proofs, an actual root, and a node list containing every node. A row certificate a contains one complete local row per node. Valid means that each row belongs to its input table and the selected rows agree on every complete edge separator. The selected family, rather than the original relations, is consistent. decode scans the supplied finite node list for an occurrence of each coordinate in the union and reads the corresponding certificate value. Applying local_row_extends_raw_join to the singleton relation containing each selected row gives one common assignment. Its restriction equalities and function extensionality identify every finite occurrence read with that assignment, reproducing each selected local row. The certificate consists of a root row and one local separator witness for each other node.

**Theorem 1.3 (Exact root decision and a reconstructed global assignment).**

$$(\forall d: SolverData, (\operatorname{isSome}\left(\operatorname{solve}\left(d\right)\right) = \operatorname{true}\left(\right) \iff \operatorname{Nonempty}\left(\operatorname{rawJoin}\left(d\right)\right)) \land (\forall j: \operatorname{Assignments}\left(\operatorname{output}\left(d\right), \operatorname{union}\left(d\right)\right), \operatorname{solve}\left(d\right) = \operatorname{some}\left(j\right) \to j \in \operatorname{rawJoin}\left(d\right)) \land (\forall e: \operatorname{Dart}\left(\operatorname{graph}\left(d\right)\right), \operatorname{card}\left(\operatorname{messageTable}\left(d, e\right)\right) \le \operatorname{power}\left(\operatorname{card}\left(\operatorname{output}\left(d\right)\right), \operatorname{card}\left(\operatorname{sep}\left(d, e\right)\right)\right) \land \operatorname{card}\left(\operatorname{sep}\left(d, e\right)\right) \le \operatorname{width}\left(d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.solve_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SolverData is the full telescope of solve_spec: the same finite input data, an actual root, complete finite node and variable lists, a complete output list and a base output. solve tests nonemptiness of rootTable, which filters the root relation against all inward tables. On acceptance an explicit finite function enumeration supplies candidate row families. Finite input-row membership and complete separator equality select a certificate; decode returns its common assignment on exactly the union. No extension, global join, or feasibility decision is assumed as an input. All semantic existence arguments occur in erased proofs.

width d is separatorWidth, the maximum cardinality of an edge separator, with maximum zero for an empty edge set. Its power bound concerns each individual separator table. It is distinct from response-state boundary width and bounds neither the sum of table sizes, retained certificates, relation storage, total memory nor total running time. The finite certificate search need not be efficient. Arbitrary finite branching, empty sensitive unions, empty separators and singleton trees remain within the quantified statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.decode_spec`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.message_table_spec`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection.solve_spec`
- Dependency: [D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages](RunningIntersectionMessages.md)
