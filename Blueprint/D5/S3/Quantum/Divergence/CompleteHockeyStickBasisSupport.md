# Complete hockey-stick contraction and basis output support

## Abstract

A condition on computational basis outputs forces unit complete hockey-stick contraction.

**Theorem 1.1 (Trivial intersection of the basis output supports).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Consider a finite channel with at least two computational basis states. If the intersection of their output supports is zero, its complete hockey-stick contraction coefficient is one at every fixed parameter greater than one.

A simplex of reference vectors makes differences between the prepared supports injective. A left inverse gives a measurement effect that annihilates the negative output terms. Its compression on the distinguished reference coordinate approaches the identity. Positive input blocks are calibrated to give two density states with the same reference marginal. The input divergence and the output effect payoff have the same normalization, so the divergence ratio approaches one using a reference of input dimension.

The simplex construction follows the common-support argument of Lluis Eriksson, Common support and complete contraction with quantum side information, v3, Section 6. The proof here uses an explicit hockey-stick difference at a fixed parameter and applies to any channel with the stated basis output supports.

**Theorem 1.2 (Calibrated basis-output witnesses).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.exists_budget_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.exists_budget_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For trivial common basis-output support, each sufficiently small positive budget is attained exactly by the input divergence on a fixed reference. Inverting the simplex normalization gives this calibration, and the graph effect gives output divergence at least a divided by (1 + D a) at budget a.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.exists_budget_witness`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.result`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation](CompleteHockeyStickRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace](../Measurement/FiniteDetectionDarkSpace.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinement](../Recovery/BKMFlagRefinement.md)
