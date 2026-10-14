# Finite instruments as a fixed quantum relation graph

## Abstract

Static relation semantics of genuine finite adaptive quantum instrument protocols.

**Theorem 1.1 (Unique local relation solution preserves every actual record).**

$$(\forall A: \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] (\forall R: \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(R\right)] (\forall F: \operatorname{Type}\left(\right), (\forall d: \operatorname{Function}\left(A, \operatorname{Nat}\left(\right)\right), (\forall T: \operatorname{FiniteLocalProtocolTree}\left(F, d\right), (\forall X: \operatorname{State}\left(R, d\right), (\exists ! phi: \operatorname{Assignment}\left(R, T\right), ((((\operatorname{GraphLaw}\left(phi\right) \land (\operatorname{rootValue}\left(phi\right) = X)) \land (\operatorname{graphLeaves}\left(phi\right) = \operatorname{terminalOutputs}\left(T, X\right))) \land (\operatorname{graphPrefixes}\left(phi\right) = \operatorname{coarsePrefixes}\left(T, X\right))) \land (\operatorname{SumTerminalTrace}\left(\operatorname{graphLeaves}\left(phi\right)\right) = \operatorname{Trace}\left(X\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph.relation_graph_protocol_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The protocol data are the canonical FiniteLocalProtocol.Tree: a finite inductive tree of completely positive instruments, finite actual outcomes, outcome-dependent interface dimensions, and a feedback value at each terminal. Each instrument is trace preserving after summing actual outcomes. Hidden Kraus labels do not control the child function. This covers arbitrary finite feedback and early termination. The input reference factor is untouched; any environment which interacts again is held in the active interface, not traced out as inaccessible garbage.

Unroll the finite actual-outcome branches into a fixed rooted graph. Put an independent full matrix variable at each prefix vertex. The graph law is only the neighboring equation X(ha)=J(a|h)(X(h)), with the canonical spectator extension on the full correlated interface. These are actual CP constraints; a global protocol equality is not a graph hypothesis. Recursion constructs one solution from the input boundary. Induction forces any other local solution to equal it at every vertex. Independently reading assigned prefix and terminal vertices gives exactly canonical coarsePrefixes and terminalOutputs, including each actual record, feedback value, interface and matrix. Canonical complete_subtree_trace gives terminal total trace on every input matrix.

The same construction works for a protocol with independent ancillary densities by applying it to appendAncillas of its input. FiniteLocalProtocol.recursive_coarse_retained preserves both all prefixes and terminals while keeping inaccessible Kraus outputs through the complete execution and tracing them only for the reported coarse output. Returning environments belong to the active system and therefore remain available to later operations. For positive trace-one input the canonical instrument semantics give nonnegative joint probabilities and total one. Born probabilities and complete positivity remain explicit quantum representation assumptions.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph.relation_graph_protocol_correspondence`
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalProtocol](../Recovery/FiniteLocalProtocol.md)
