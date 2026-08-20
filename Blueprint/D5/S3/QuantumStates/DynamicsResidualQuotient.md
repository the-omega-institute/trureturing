# Dynamics on the Final Orthogonal Residual

## Abstract

The orthogonal residual of the adjoint observable closure is invariant and has a quotient dynamics.

**Theorem 1.1 (The final orthogonal residual is invariant and quotients the dynamics).**

$$\forall V: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}_{\mathbb{R}}(V)], [\operatorname{FiniteDimensional}_{\mathbb{R}}(V)],\ K: \operatorname{LinearMap}_{\mathbb{R}}(V \to V), Phi: \operatorname{LinearMap}_{\mathbb{R}}(V \to V), W: \operatorname{Submodule}(\mathbb{R}, V),\ \forall x, a, \operatorname{inner}(\mathbb{R}, Phi(x), a) = \operatorname{inner}(\mathbb{R}, x, K(a)) \Rightarrow\ (\forall x, x \in \operatorname{observableClosure}(K, W)^{\perp}, Phi(x) \in \operatorname{observableClosure}(K, W)^{\perp}) \land \\\exists induced: \operatorname{LinearMap}_{\mathbb{R}}(\operatorname{Quotient}(\operatorname{observableClosure}(K, W)^{\perp}) \to \operatorname{Quotient}(\operatorname{observableClosure}(K, W)^{\perp})), \forall x, induced(\operatorname{mkQ}(\operatorname{observableClosure}(K, W)^{\perp}, x)) = \operatorname{mkQ}(\operatorname{observableClosure}(K, W)^{\perp}, Phi(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/DynamicsResidualQuotient.dynamics_residual_invariant_and_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible space is constructed from every forward iterate of the adjoint observable map K applied to the source visible subspace W. The final residual is its orthogonal complement.

The displayed adjoint pairing transfers orthogonality from the residual through Phi, yielding Phi(R) contained in R. The canonical quotient lift then constructs the induced linear map and its projection law.

Repository search found no packaged theorem containing all clauses. Pinned Mathlib supplies and is applied through Submodule.mem_orthogonal', Submodule.liftQ, Submodule.liftQ_apply, and Submodule.Quotient.mk_eq_zero.

## References

- Truth anchor: `D5/S3/QuantumStates/DynamicsResidualQuotient.dynamics_residual_invariant_and_quotient`
