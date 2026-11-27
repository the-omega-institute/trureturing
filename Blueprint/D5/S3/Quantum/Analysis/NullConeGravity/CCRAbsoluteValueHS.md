# Absolute values in the Hilbert–Schmidt ideal

## Abstract

Hilbert–Schmidt estimates for operator absolute values and adjoints.

The comparison of normalized covariance roots uses a Hilbert–Schmidt absolute-value bound. It applies to the square-root perturbations in Eq. (71) of Satishchandran and Sorce.

**Definition 1.1 (Operator absolute value).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the positive square root of the adjoint times the operator.

**Theorem 1.2 (Self-adjoint contraction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_selfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For bounded self-adjoint operators with Hilbert–Schmidt difference, the difference of their absolute values is Hilbert–Schmidt with squared norm at most that of the original difference. In finite dimension, expand in a mixed pair of orthonormal eigenbases and apply the scalar absolute-value contraction to each coefficient. The finite compressions converge strongly. Uniform polynomial approximation preserves this convergence under absolute value, so each finite column sum passes to the limit under the same bound.

**Definition 1.3 (Two-copy dilation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.dilation`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.dilation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On the Hilbert sum of two copies, the dilation applies the adjoint to the second coordinate and the original operator to the first coordinate, giving the two output coordinates in that order.

**Theorem 1.4 (Self-adjoint dilation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.dilation_isSelfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.dilation_isSelfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The two off-diagonal blocks are adjoints, so the dilation is self-adjoint.

**Theorem 1.5 (Absolute value of the dilation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_dilation_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_dilation_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The two diagonal entries are the absolute values of the operator and its adjoint. They are positive and their block diagonal square is the square of the dilation.

**Theorem 1.6 (Symmetric squared estimate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For two bounded operators with Hilbert–Schmidt difference, both absolute-value differences, for the operators and for their adjoints, are Hilbert–Schmidt. The sum of their squared norms is at most twice the squared norm of the original difference. Apply the self-adjoint contraction to the dilations and split the column sums over the two copies.

**Theorem 1.7 (Squared estimate for arbitrary operators).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The squared Hilbert–Schmidt norm of the difference of absolute values is at most twice that of the difference of the operators, by nonnegativity of the adjoint contribution.

**Theorem 1.8 (Equality on the complex line).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_symmetric_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_symmetric_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The identity and zero operators on the complex line have input squared norm one and joint output squared norm two. Thus the factor in the symmetric estimate is attained.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.dilation`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.dilation_isSelfAdjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_dilation_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_symmetric`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.opAbs_sub_symmetric_sharp`
- Dependency: [D5/S3/Quantum/Analysis/CompactEigenbasis](../CompactEigenbasis.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation](CCRConjugation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](../TraceClass/HilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/LogRegularization](../TraceClass/LogRegularization.md)
