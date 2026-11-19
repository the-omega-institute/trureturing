# Support-Aware Quantum Relative Entropy

## Abstract

Quantum trace-log relative entropy is extended by top exactly outside support inclusion.

**Theorem 1.1 (A faithful second state has full support).**

Lean statement: `D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.support_of_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.support_of_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive definite matrix has zero nullspace. Its density state therefore contains the support of every first state.

**Theorem 1.2 (The infinite branch is exactly support failure).**

$$\operatorname{extendedQuantumRelativeEntropy}(\rho, \sigma) = \infty \iff \neg\operatorname{SupportContained}(\rho, \sigma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_top_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Support containment is frozen as reverse inclusion of matrix nullspaces: every vector annihilated by the second state is annihilated by the first.

The extended entropy takes values in the reals with top adjoined. On supported pairs it is the finite trace-log branch; outside support inclusion it is exactly top.

Positivity, data-processing, and Petz equality are deliberately left as separate future theorems on this carrier.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_top_iff`
- Truth anchor: `D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.support_of_posDef`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
