# Disjoint quantum ports and topological-order independence

## Abstract

Disjoint quantum ports and topological-order independence

**Theorem 1.1 (Actual disjoint Kraus ports interchange on correlated matrices).**

$$(\forall I: \operatorname{Type}\left(\right), (\forall J: \operatorname{Type}\left(\right), (\forall O: \operatorname{Type}\left(\right), (\forall P: \operatorname{Type}\left(\right), (\forall M: \operatorname{Type}\left(\right), (\forall N: \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(J\right)] [\operatorname{DecidableEq}\left(J\right)] [\operatorname{Fintype}\left(O\right)] [\operatorname{DecidableEq}\left(O\right)] [\operatorname{Fintype}\left(P\right)] [\operatorname{DecidableEq}\left(P\right)] [\operatorname{Fintype}\left(M\right)] [\operatorname{Fintype}\left(N\right)] (\forall A: \operatorname{KrausFamily}\left(M, O, I\right), (\forall B: \operatorname{KrausFamily}\left(N, P, J\right), (\forall rho: \operatorname{State}\left(\operatorname{Product}\left(I, J\right)\right), (\operatorname{rightBranch}\left(B, \operatorname{leftBranch}\left(A, rho\right)\right) = \operatorname{leftBranch}\left(A, \operatorname{rightBranch}\left(B, rho\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteCausalPortGraph.disjoint_port_interchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The two branches act as A tensor identity and identity tensor B on the full joint matrix. Rectangular Kronecker multiplication identifies either composed Kraus operator with A tensor B. Interchanging the finite hidden-label sums then proves the equality without requiring a product input or assuming commutation.

**Theorem 1.2 (Disjoint quantum ports and topological-order independence).**

$$(\forall E: \operatorname{Type}\left(\right), [\operatorname{PartialOrder}\left(E\right)] (\forall G: \operatorname{QuantumPortGraph}\left(E\right), (\forall h: \operatorname{Records}\left(\operatorname{Outcomes}\left(G\right)\right), (\forall K: \operatorname{Set}\left(E\right), (\forall L: \operatorname{Set}\left(E\right), (\forall l: \operatorname{List}\left(E\right), (\forall m: \operatorname{List}\left(E\right), (\forall X: \operatorname{State}\left(\operatorname{Cut}\left(G, K\right)\right), (((((\operatorname{IsLowerSet}\left(K\right) \land \operatorname{IsLowerSet}\left(L\right)) \land \operatorname{Finite}\left(L\right)) \land \operatorname{Exec}\left(K, l, L\right)) \land \operatorname{Exec}\left(K, m, L\right)) \implies (\operatorname{pathMap}\left(\operatorname{Readout}\left(G, h\right), l, X\right) = \operatorname{pathMap}\left(\operatorname{Readout}\left(G, h\right), m, X\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteCausalPortGraph.quantum_schedule_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

Every cut has a finite complex matrix interface. A local instrument has finitely many actual outcomes and hidden Kraus labels, rectangular Kraus matrices, and sum over outcomes and hidden labels of K-adjoint K equal to identity. Its combined channel is the canonical FiniteKrausChannel supplier. Branch matrices are actual sums K X K-adjoint, not abstract state-transforming functions. Cut matrices include joint correlations, reference systems, observers, memories and every environment that can interact again.

Acting on one tensor port uses K tensor identity on the complete joint matrix. Rectangular Kronecker multiplication and exchanging the two finite hidden sums show that two disjoint local operations commute on every matrix, including entangled inputs. PortSquare certifies the individual four edge maps as the two corresponding spectator lifts in explicit tensor coordinates. It supplies neither a diamond equation nor a whole-path interchange law. The diamond is derived from these actual quantum interfaces.

An event chooses its Kraus instrument only from the already available record and its own actual outcome. The derived local diamonds and ConfigurationPathTransport finite-endpoint path theorem imply equality of the complete cut matrix for any two legal topological schedules and a fixed event-indexed actual record. Projecting to a subsystem or an effect preserves that equality. The literal occurrence history is not deleted or identified with the output matrix.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteCausalPortGraph.disjoint_port_interchange`
- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteCausalPortGraph.quantum_schedule_independence`
- Dependency: [D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport](../../ConceptDynamics/Fibers/ConfigurationPathTransport.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity](../../ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
