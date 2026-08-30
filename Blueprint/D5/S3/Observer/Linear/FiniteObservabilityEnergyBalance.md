# Finite Observability Energy Balance

## Abstract

The finite observability Gramian telescopes, is positive semidefinite, and measures state energy loss.

**Theorem 1.1 (Finite observability identity and energy balance).**

$$\begin{aligned}\forall K, V, Y: \operatorname{Type},\\{}[\operatorname{RCLike}(K)] \land [\operatorname{NormedAddCommGroup}(V)] \land [\operatorname{InnerProductSpace}(K, V)] \land [\operatorname{FiniteDimensional}(K, V)] \land\\{}[\operatorname{NormedAddCommGroup}(Y)] \land [\operatorname{InnerProductSpace}(K, Y)] \land [\operatorname{FiniteDimensional}(K, Y)] \land\\\forall A: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y), N: \mathbb{N}, (\operatorname{adjoint}(A) \circ A) + (\operatorname{adjoint}(C) \circ C) = \operatorname{id}() \Rightarrow\\{}\\{}\operatorname{id}() - (\operatorname{adjoint}(A^{N}) \circ A^{N}) = \sum_{k\in\operatorname{range}(N)} (\operatorname{adjoint}(A^{k}) \circ (\operatorname{adjoint}(C) \circ C) \circ A^{k}) \land \forall x: V, 0 \le \Re(\langle x, \sum_{k\in\operatorname{range}(N)} (\operatorname{adjoint}(A^{k}) \circ (\operatorname{adjoint}(C) \circ C) \circ A^{k})(x) \rangle) \land \forall x: V, \left\lVert x \right\rVert^{2} - \left\lVert (A^{N} x) \right\rVert^{2} = \sum_{k\in\operatorname{range}(N)} \left\lVert (C A^{k} x) \right\rVert^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FiniteObservabilityEnergyBalance.finite_observability_energy_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The update A and readout C act on finite-dimensional inner-product spaces over a real or complex scalar field. The conservation law A* A + C* C = I is the source premise.

The finite Gramian is the explicit sum of the adjoint readout terms for k below N. The first public clause telescopes this sum against the N-step state operator.

The second clause states positive semidefiniteness as nonnegativity of every quadratic form. The third clause gives the corresponding finite state norm-energy balance.

Repository and pinned-library searches found no packaged theorem with all three clauses. The proof applies the adjoint-power law, finite sum telescoping, and adjoint inner-product identities directly.

## References

- Truth anchor: `D5/S3/Observer/Linear/FiniteObservabilityEnergyBalance.finite_observability_energy_balance`
