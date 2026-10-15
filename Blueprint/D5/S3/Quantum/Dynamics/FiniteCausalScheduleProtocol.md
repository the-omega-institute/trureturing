# Finite causal schedules as executable quantum relation graphs

## Abstract

Finite causal schedules as executable quantum relation graphs

**Theorem 1.1 (Finite adaptive programs have a unique normalized static relation solution).**

$$(\forall I: \operatorname{Interface}\left(\right), (\forall P: \operatorname{Program}\left(I\right), (\forall X: \operatorname{CutState}\left(I\right), (\exists ! phi: \operatorname{Assignment}\left(P\right), ((\operatorname{GraphLaw}\left(phi\right) \land (\operatorname{rootValue}\left(phi\right) = X)) \land (\operatorname{SumTerminalTrace}\left(\operatorname{leaves}\left(phi\right)\right) = \operatorname{Trace}\left(X\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol.program_graph_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The program is a finite tree of actual normalized Kraus instruments. A child is selected by the observed outcome alone. Independently assigned prefix matrices satisfying only the local equations are uniquely reconstructed from the root, and terminal trace equals the root trace on every input matrix. Positive input gives positive terminal matrices by rectangular Kraus conjugation and finite positive sums.

**Theorem 1.2 (Finite causal schedules as executable quantum relation graphs).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall G: \operatorname{QuantumPortGraph}\left(E\right), (\forall K: \operatorname{Set}\left(E\right), (\forall L: \operatorname{Set}\left(E\right), (\forall l: \operatorname{List}\left(E\right), (\forall h: \operatorname{Records}\left(\operatorname{Outcomes}\left(G\right)\right), (\forall X: \operatorname{State}\left(\operatorname{Cut}\left(G, K\right)\right), ((((\operatorname{Exec}\left(K, l, L\right) \land \operatorname{IsLowerSet}\left(K\right)) \land \operatorname{IsLowerSet}\left(L\right)) \land \operatorname{Finite}\left(L\right)) \implies (\exists ! phi: \operatorname{Assignment}\left(\operatorname{compile}\left(G, l, \operatorname{RestrictRecord}\left(h, K\right)\right)\right), (((((\operatorname{GraphLaw}\left(phi\right) \land (\operatorname{rootValue}\left(phi\right) = X)) \land (\operatorname{SumTerminalTrace}\left(\operatorname{leaves}\left(phi\right)\right) = \operatorname{Trace}\left(X\right))) \land \operatorname{Member}\left(\operatorname{RecordedTerminal}\left(\operatorname{ScheduledOutcomes}\left(l, h\right), \operatorname{Cut}\left(G, L\right), \operatorname{pathMap}\left(\operatorname{Readout}\left(G, h\right), l, X\right)\right), \operatorname{leaves}\left(phi\right)\right)) \land (\forall m: \operatorname{List}\left(E\right), (\operatorname{Exec}\left(K, m, L\right) \implies (\operatorname{pathMap}\left(\operatorname{Readout}\left(G, h\right), l, X\right) = \operatorname{pathMap}\left(\operatorname{Readout}\left(G, h\right), m, X\right))))) \land (\forall z: \operatorname{Terminal}\left(\right), (\operatorname{Member}\left(z, \operatorname{leaves}\left(phi\right)\right) \implies (\operatorname{HistoryLength}\left(z\right) = \operatorname{Ncard}\left(\operatorname{Difference}\left(L, K\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol.causal_schedule_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The compiler reads a finite legal event schedule. At each step it constructs the actual normalized instrument from the graph Kraus data, branches on its finite observed outcome, extends only the observed record, and recursively compiles the remaining positive event occurrences. Hidden Kraus labels are summed and never control feedback. The resulting Program has concrete finite interfaces and a structurally finite termination bound equal to the schedule length. Every terminal record has this length, and the finite history clock theorem identifies it with the cardinality of the added event occurrences.

Independently assign matrices to all observed-prefix vertices of this executable tree. The graph law contains only neighboring CP equations. Recursion constructs a solution from any input boundary, and induction gives uniqueness. Terminal total trace equals input trace by the canonical CPTP supplier at each node. Early termination is admitted by the stop instruction. A fixed actual record selects an existing compiled terminal whose history is precisely the scheduled observed outcomes and whose full matrix is the original path composite.

For different legal topological schedules compare event-indexed records, rather than their differently ordered output strings. Derived disjoint-port interchange gives the same complete final matrix for every record and therefore the same joint probabilities and reference-boundary readouts. Conversely these local normalized instructions constitute a legal finite adaptive quantum protocol. FiniteInstrumentRelationGraph gives the corresponding construction directly for the canonical protocol Tree, including outcome-dependent dimensions, reference factors, independent ancillary densities, retained returning environments and early leaves.

A finite deterministic causal DAG can be executed in a topological order, as in Chiribella, D’Ariano and Perinotti, Theoretical framework for quantum networks (arXiv:0904.4483v2), Section II.C.1. Finite actual-outcome feedback unrolls it into a finite tree of real instruments; this is a fixed relation graph with a variable at every actual prefix. Finite Kraus representation is the existing quantum-foundation input for CP nodes, while unused external systems remain spectator coordinates and a returning environment remains an active port. All distributions are the prescribed instrument Born probabilities. Static representation does not derive the Born law, permit an infinite output interface, discard a returning environment, or erase positive occurrences.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol.causal_schedule_realization`
- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol.program_graph_correspondence`
- Dependency: [D5/S3/Quantum/Dynamics/FiniteCausalPortGraph](FiniteCausalPortGraph.md)
- Dependency: [D5/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph](FiniteInstrumentRelationGraph.md)
