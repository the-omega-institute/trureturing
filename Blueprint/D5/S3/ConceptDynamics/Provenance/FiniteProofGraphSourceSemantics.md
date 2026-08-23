# Finite Proof-Graph Source Semantics

## Abstract

Finite acyclic source semantics is equivalent to a source-supported proof path.

**Theorem 1.1 (Source semantics is exactly valid source-path reachability).**

$$\forall n, graph: FiniteAcyclicProofGraph(n), sources: Finset(Fin(n)), target: Fin(n),\\{}sourceSemantic(graph, sources, target) \iff \exists path: List(Fin(n)), ValidProofPath(graph, sources, target, path).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/FiniteProofGraphSourceSemantics.source_semantic_iff_valid_source_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite graph is represented on Fin n. Its edge relation carries a strictly increasing natural-number rank, which is a constructive certificate that no directed cycle can occur.

A valid proof path is a nonempty finite list whose first vertex belongs to the available source set, whose adjacent vertices are graph edges, and whose final vertex is the requested conclusion.

The proposition sourceSemantic graph sources target is the formal counterpart of the source's phi_c(S)=True condition. The theorem states exactly that this condition holds if and only if such a source-supported valid path exists.

Repository and pinned-library searches found no canonical directed proof-graph source-semantics carrier or theorem. The local definitions therefore record the source's finite graph and path semantics directly; the equivalence is definitional.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/FiniteProofGraphSourceSemantics.source_semantic_iff_valid_source_path`
