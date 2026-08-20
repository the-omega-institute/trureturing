# Unique Descent on the Final Orthogonal Residual

## Abstract

The orthogonal residual of an iterated observable closure is invariant and has a unique quotient descent.

**Theorem 1.1 (The final orthogonal residual is invariant and has a unique quotient descent).**

$$\forall V: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}_{\mathbb{R}}(V)], [\operatorname{FiniteDimensional}_{\mathbb{R}}(V)],\ K: \operatorname{LinearMap}_{\mathbb{R}}(V \to V), Phi: \operatorname{LinearMap}_{\mathbb{R}}(V \to V), W: \operatorname{Submodule}(\mathbb{R}, V),\ \forall x, a, \operatorname{inner}(\mathbb{R}, Phi(x), a) = \operatorname{inner}(\mathbb{R}, x, K(a)) \Rightarrow\ (\forall x, x \in \operatorname{observableClosureUnique}(K, W)^{\perp}, Phi(x) \in \operatorname{observableClosureUnique}(K, W)^{\perp}) \land \\\exists induced: \operatorname{LinearMap}_{\mathbb{R}}(\operatorname{Quotient}(\operatorname{observableClosureUnique}(K, W)^{\perp}) \to \operatorname{Quotient}(\operatorname{observableClosureUnique}(K, W)^{\perp})), (\forall x, induced(\operatorname{mkQ}(\operatorname{observableClosureUnique}(K, W)^{\perp}, x)) = \operatorname{mkQ}(\operatorname{observableClosureUnique}(K, W)^{\perp}, Phi(x)) \land \forall other: \operatorname{LinearMap}_{\mathbb{R}}(\operatorname{Quotient}(\operatorname{observableClosureUnique}(K, W)^{\perp}) \to \operatorname{Quotient}(\operatorname{observableClosureUnique}(K, W)^{\perp})), \forall x, other(\operatorname{mkQ}(\operatorname{observableClosureUnique}(K, W)^{\perp}, x)) = \operatorname{mkQ}(\operatorname{observableClosureUnique}(K, W)^{\perp}, Phi(x)) \Rightarrow other = induced).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/DynamicsResidualQuotientUnique.dynamics_residual_invariant_and_unique_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible space is constructed from every forward iterate of the adjoint observable map K applied to the source visible subspace W. The residual is its orthogonal complement.

The adjoint pairing transfers orthogonality through Phi, and the public existence-unique clause states that exactly one linear map on the quotient satisfies the projection law.

Repository search found no exact theorem packaging the invariant residual with unique quotient descent. Pinned Mathlib supplies and is applied through Submodule.mem_orthogonal', Submodule.liftQ, Submodule.liftQ_apply, Submodule.Quotient.mk_eq_zero, and Submodule.mkQ_surjective.

## References

- Truth anchor: `D5/S3/QuantumStates/DynamicsResidualQuotientUnique.dynamics_residual_invariant_and_unique_quotient`
