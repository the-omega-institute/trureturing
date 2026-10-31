# Specht ComplexIrreducibility

## Abstract

Specht ComplexIrreducibility

The intertwining condition is the kernel of the linear map recording commutation defects. Finite free scalar extension identifies the ambient linear-map spaces, and flatness preserves the kernel. The intertwiner dimension survives complexification. Rational scalarity makes the complex endomorphism space one dimensional. The finite-group character norm criterion gives simplicity of the complex scalar extension of the same literal partition-indexed Specht module. The three-row Cauchy and mixed pairings supply the subsequent comparison with the Frobenius coefficient.

ModuleOver means an additive commutative group with the indicated module structure in the intertwiner statements. In the semiring action identity it means an additive commutative monoid with that module structure. FiniteMonoid includes no commutativity assumption. The linear equivalence by flat kernel base change maps the scalar extension of the original intertwiner space to the intertwiners between the two extended actions.

**Theorem 1.1 (isBaseChange baseChangeHom).**

$$\forall R \in \operatorname{Type},\; \forall A \in \operatorname{Type},\; \forall M \in \operatorname{Type},\; \forall N \in \operatorname{Type},\; (\operatorname{CommSemiring}\left(R\right)) \Rightarrow ((\operatorname{CommSemiring}\left(A\right)) \Rightarrow ((\operatorname{Algebra}\left(R, A\right)) \Rightarrow ((\operatorname{AddCommMonoid}\left(M\right)) \Rightarrow ((\operatorname{Module}\left(R, M\right)) \Rightarrow ((\operatorname{ModuleFree}\left(R, M\right)) \Rightarrow ((\operatorname{ModuleFinite}\left(R, M\right)) \Rightarrow ((\operatorname{AddCommMonoid}\left(N\right)) \Rightarrow ((\operatorname{Module}\left(R, N\right)) \Rightarrow (\operatorname{IsBaseChange}\left(A, \operatorname{linearMapBaseChangeHom}\left(R, A, M, N\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.isBaseChange_baseChangeHom` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Theorem 1.2 (baseChange apply).**

$$\forall R \in \operatorname{CommSemiring},\; \forall A \in \operatorname{SemiringAlgebraOver}\left(R\right),\; \forall G \in \operatorname{Monoid},\; \forall V \in \operatorname{ModuleOver}\left(R\right),\; \forall rho \in \operatorname{Representation}\left(R, G, V\right),\; \forall g \in G,\; \operatorname{action}\left(\operatorname{baseChange}\left(A, rho\right), g\right) = \operatorname{linearMapBaseChange}\left(A, \operatorname{action}\left(rho, g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.baseChange_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Definition 1.3 (intertwiningMapBaseChangeEquiv).**

$$\forall K \in \operatorname{CommRing},\; \forall L \in \operatorname{CommRingAlgebraOver}\left(K\right),\; \forall G \in \operatorname{FiniteMonoid},\; \forall V \in \operatorname{FiniteFreeModuleOver}\left(K\right),\; \forall W \in \operatorname{ModuleOver}\left(K\right),\; (\operatorname{ModuleFlat}\left(K, L\right)) \Rightarrow (\forall rho \in \operatorname{Representation}\left(K, G, V\right),\; \forall sigma \in \operatorname{Representation}\left(K, G, W\right),\; \operatorname{intertwiningMapBaseChangeEquiv}\left(rho, sigma\right) = \operatorname{linearEquivalenceByFlatKernelBaseChange}\left(L, \operatorname{Intertwiner}\left(rho, sigma\right), \operatorname{Intertwiner}\left(\operatorname{baseChange}\left(L, rho\right), \operatorname{baseChange}\left(L, sigma\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.intertwiningMapBaseChangeEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Theorem 1.4 (finrank intertwiningMap baseChange).**

$$\forall K \in \operatorname{Field},\; \forall L \in \operatorname{NontrivialCommRingAlgebraOver}\left(K\right),\; \forall G \in \operatorname{FiniteMonoid},\; \forall V \in \operatorname{FiniteDimensionalModuleOver}\left(K\right),\; \forall W \in \operatorname{ModuleOver}\left(K\right),\; \forall rho \in \operatorname{Representation}\left(K, G, V\right),\; \forall sigma \in \operatorname{Representation}\left(K, G, W\right),\; \operatorname{finrank}\left(L, \operatorname{Intertwiner}\left(\operatorname{baseChange}\left(L, rho\right), \operatorname{baseChange}\left(L, sigma\right)\right)\right) = \operatorname{finrank}\left(K, \operatorname{Intertwiner}\left(rho, sigma\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.finrank_intertwiningMap_baseChange` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Theorem 1.5 (spechtModuleℂ def).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{spechtModuleComplex}\left(mu\right) = \operatorname{FDRepOf}\left(\operatorname{baseChange}\left(\operatorname{Complex}, \operatorname{rationalSpechtAction}\left(mu\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.spechtModuleℂ_def` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Theorem 1.6 (instSimpleSpechtModuleℂ).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{Simple}\left(\operatorname{spechtModuleComplex}\left(mu\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.instSimpleSpechtModuleℂ` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.baseChange_apply`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.finrank_intertwiningMap_baseChange`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.instSimpleSpechtModuleℂ`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.intertwiningMapBaseChangeEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.isBaseChange_baseChangeHom`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.spechtModuleℂ_def`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility](SpechtAbsoluteIrreducibility.md)
