# Complete hockey-stick contraction and Choi support

## Abstract

The absence of a full reference factor in the Choi support forces unit complete hockey-stick contraction at every parameter greater than one.

**Theorem 1.1 (Unit contraction from the normalized Choi support).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Fix a finite channel with nonempty input and a hockey-stick parameter greater than one. If the support of the normalized Choi matrix contains no full reference factor over a nonzero output vector, the complete coefficient for equal-reference-marginal inputs is one.

Unitary matrices span the reference matrix algebra. Matrix units then recover every output slice of a common support vector. Finite dimensionality reduces the zero intersection to finitely many translates. Preparing the corresponding Bell states gives these translates as basis outputs. The prepared inputs share the added marginal I divided by the input dimension. Data processing bounds the prepared denominator between the output divergence and the original denominator, so each positive output ratio can only increase under this transfer.

The basis-output support theorem uses the simplex mechanism from Eriksson, Common support and complete contraction with quantum side information, v3, Section 6. Eriksson's criterion concerns Umegaki relative entropy for classical-input channels. The simplex bound used here holds pointwise at the fixed hockey-stick parameter.

**Theorem 1.2 (Contraction bound from a replacement component).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.coefficient_le_of_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.coefficient_le_of_replacement` (`✓ std3`). ∎

*Citation.* Ian George; Christoph Hirche; Theshani Nuradha; Mark M. Wilde (2026). *Quantum Doeblin Coefficients: Interpretations and Applications*. DOI: [10.22331/q-2026-05-22-2115](https://doi.org/10.22331/q-2026-05-22-2115). URL: <https://arxiv.org/html/2503.22823v3>.

*Commentary.*

A channel with a replacement component of weight p has complete coefficient at most one minus p for every parameter at least one. Equal input reference marginals make the replacement term in the amplified hockey-stick difference negative semidefinite. Monotonicity of the positive-part trace and data processing for the residual channel give the bound. This is the bound for an exhibited weight in Proposition 31 of George, Hirche, Nuradha and Wilde.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.coefficient_le_of_replacement`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.result`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport](CompleteHockeyStickBasisSupport.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiKernelContraction](UmegakiKernelContraction.md)
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction](../ProcessReconstruction/LiuWildChoiObstruction.md)
