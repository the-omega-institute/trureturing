# Running Intersection Records

## Abstract

Running intersection identifies full cut boundaries and lets every specified local row extend to a raw global record on a finite tree.

Node indexes scopes S and local relations Gamma. Variables and their dependent value types are arbitrary; scopes and relations may be infinite. An assignment on U_A supplies precisely the variables occurring in A. J_A is the raw join requiring each node restriction to belong to its local relation. The empty join is the singleton canonical empty assignment. These are the existing HistoryPayloadFactorization assignment and join definitions.

**Definition 1.1 (Connected occurrences).**

$$\operatorname{RI}\left(T, S\right) \iff \forall x, \operatorname{Preconnected}\left(\operatorname{induce}\left(T, \operatorname{Occ}\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.RunningIntersection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RI requires each occurrence-induced graph to be preconnected. When a variable occurs, this is connectedness; absent variables impose no condition. In an acyclic graph, the unique ambient path between two occurrences stays within their occurrence set.

**Definition 1.2 (An actual deleted-edge component).**

$$\operatorname{L}\left(e\right) = \operatorname{ReachableSet}\left(\operatorname{deleteEdges}\left(T, \operatorname{singleton}\left(\operatorname{edge}\left(e\right)\right)\right), \operatorname{fst}\left(e\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.edgeLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L is defined by reachability from the first endpoint after deleting the chosen edge. Its complementary set is R.

**Theorem 1.3 (Exactly two endpoint components).**

$$\operatorname{IsTree}\left(T\right) \to \operatorname{complement}\left(\operatorname{L}\left(e\right)\right) = \operatorname{ReachableSet}\left(\operatorname{deleteEdges}\left(T, \operatorname{singleton}\left(\operatorname{edge}\left(e\right)\right)\right), \operatorname{snd}\left(e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.edge_cut_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first endpoint belongs to L and the second does not. Every connected component of the deleted graph is one of the two endpoint components. This topology requires the tree hypothesis and requires no RI.

**Theorem 1.4 (The full boundary of any region).**

$$\operatorname{RI}\left(T, S\right) \to \operatorname{intersection}\left(\operatorname{U}\left(A\right), \operatorname{U}\left(\operatorname{complement}\left(A\right)\right)\right) = \operatorname{unionCrossingSeparators}\left(T, S, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.boundary_eq_union_separators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary A, its full overlap with the complement is the union of S_p intersect S_q over edges with p in A and q outside A. An occurrence walk crosses the inverse image of A inside the occurrence-induced graph. No tree or finiteness assumption is needed. The boundary value is one dependent assignment on this entire union, including when the complement is disconnected; complete complement records already agree on shared variables.

**Theorem 1.5 (A cut overlap equals its separator).**

$$\operatorname{IsTree}\left(T\right) \land \operatorname{RI}\left(T, S\right) \to \operatorname{intersection}\left(\operatorname{U}\left(\operatorname{L}\left(e\right)\right), \operatorname{U}\left(\operatorname{complement}\left(\operatorname{L}\left(e\right)\right)\right)\right) = \operatorname{intersection}\left(\operatorname{S}\left(\operatorname{fst}\left(e\right)\right), \operatorname{S}\left(\operatorname{snd}\left(e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.cut_scope_eq_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the deleted edge crosses its two components. RI therefore identifies the complete component overlap with the complete edge separator.

**Theorem 1.6 (Unique gluing of two fixed records).**

$$\exists! j: J, \operatorname{restrict}\left(j, L\right) = a \land \operatorname{restrict}\left(j, R\right) = b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.cut_records_glue_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a complete record a on L and b on R whose edge-separator restrictions agree, there is exactly one raw global record with those two restrictions. The tree and RI assumptions justify replacing full overlap by the edge separator. Full-overlap gluing itself requires neither assumption, and local relations may be empty. This is uniqueness for fixed a and b.

**Definition 1.7 (Equality of complete projection images).**

$$\forall p, q, \operatorname{Adj}\left(T, p, q\right) \to \operatorname{project}\left(\operatorname{Gamma}\left(p\right), \operatorname{C}\left(p, q\right)\right) = \operatorname{project}\left(\operatorname{Gamma}\left(q\right), \operatorname{C}\left(p, q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.EdgeProjectionConsistency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C_pq is S_p intersect S_q. Both images are sets of complete dependent assignments on C_pq; equality matches whole separator records.

**Theorem 1.8 (Preserve a whole partial record).**

$$\forall a: \operatorname{J}\left(A\right), \exists b: \operatorname{J}\left(\operatorname{union}\left(A, \operatorname{singleton}\left(q\right)\right)\right), \operatorname{restrict}\left(b, \operatorname{U}\left(A\right)\right) = a$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.extend_record_at_neighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a tree, RI, complete edge projection consistency, a connected induced region A, and an edge from p in A to q outside A. The restriction of a to S_p supplies a matching Gamma_q row. The overlap U_A intersect S_q equals C_pq. Gluing on the node set A union {q} preserves every previous coordinate and uses no records outside that set.

**Theorem 1.9 (Every specified row extends).**

$$\forall r, a \in \operatorname{Gamma}\left(r\right), \exists j: J, \operatorname{restrict}\left(j, \operatorname{S}\left(r\right)\right) = a$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.local_row_extends_raw_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume finite Node, a tree, RI, nonempty local relations and equality of complete edge projection images. Tree connectedness supplies nonempty Node. Starting with the specified row, each growth step preserves the entire previous assignment and reduces the finite complement until all nodes are included. Global extension is existential and need not be unique. For any additional constraint K, actual worlds are W = J intersect K; raw extension does not assert W is nonempty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.EdgeProjectionConsistency`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.RunningIntersection`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.boundary_eq_union_separators`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.cut_records_glue_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.cut_scope_eq_separator`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.edgeLeft`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.edge_cut_components`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.extend_record_at_neighbor`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.local_row_extends_raw_join`
- Dependency: [D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization](../Observation/HistoryPayloadFactorization.md)
