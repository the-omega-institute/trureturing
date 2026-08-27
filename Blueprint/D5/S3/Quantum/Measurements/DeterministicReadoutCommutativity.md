# Deterministic Readout Commutativity

## Abstract

Deterministic readout projections share a diagonal basis, while general quantum observables need not commute.

**Theorem 1.1 (Common-basis projections commute; a qubit pair is noncommuting).**

$$\forall X: \operatorname{Type}, O: \operatorname{Type}, I: \operatorname{Type}, [\operatorname{Fintype}(X)], [\operatorname{DecidableEq}(X)], [\operatorname{DecidableEq}(O)], q: I \to X \to O \Rightarrow \forall i: I, j: I, o: O, op: O, \operatorname{deterministicProjection}(\operatorname{q}(i), o) \circ \operatorname{deterministicProjection}(\operatorname{q}(j), op) = \operatorname{deterministicProjection}(\operatorname{q}(j), op) \circ \operatorname{deterministicProjection}(\operatorname{q}(i), o) \land \exists P, Q : \operatorname{QubitMatrix}(), \operatorname{star}(P) = P \land \operatorname{star}(Q) = Q \land P \circ P = I \land Q \circ Q = I \land P \circ Q \neq Q \circ P.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/DeterministicReadoutCommutativity.deterministic_readout_commutes_and_quantum_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every deterministic interface is represented by diagonal indicators of its readout fibers in one standard basis, so all such projections commute.

The reverse inclusion fails: the Pauli qubit pair is self-adjoint, squares to the identity, and has unequal products in the two orders.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/DeterministicReadoutCommutativity.deterministic_readout_commutes_and_quantum_counterexample`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Measurements/DeterministicReadoutPvm](DeterministicReadoutPvm.md)
