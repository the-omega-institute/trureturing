# The Joint Kernel of All Finite Quotients

## Abstract

All finite quotients jointly detect exactly the complement of the finite residual.

**Theorem 1.1 (The joint finite-quotient kernel is the finite residual).**

$$\operatorname{ker}\left(\operatorname{finiteQuotientObserver}\left(G\right)\right) = \operatorname{finiteResidual}\left(G\right) \land \left(\left(\operatorname{ResiduallyFinite}\left(G\right) \Leftrightarrow \operatorname{finiteResidual}\left(G\right) = \operatorname{trivialSubgroup}\left(G\right)\right) \land \left(\operatorname{finiteResidual}\left(G\right) = \operatorname{trivialSubgroup}\left(G\right) \Leftrightarrow \operatorname{Injective}\left(\operatorname{finiteQuotientObserver}\left(G\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel.finite_quotient_joint_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each finite-index normal subgroup H, the canonical observation sends a group element to its class in G/H. The joint observer records these classes for every such H.

An element is in the kernel of the joint observer exactly when it belongs to every finite-index normal subgroup. This intersection is the finite residual.

Mathlib's residual-finiteness criterion identifies this intersection with the trivial subgroup, while the standard homomorphism-kernel criterion identifies trivial kernel with injectivity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel.finite_quotient_joint_kernel`
