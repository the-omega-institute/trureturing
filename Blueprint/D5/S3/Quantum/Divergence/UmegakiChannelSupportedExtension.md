# Complete and conditional Umegaki coefficients

## Abstract

The supported entropy coefficients coincide and are attained by the left endpoint of the arithmetic metric family.

**Definition 1.1 (Complete Umegaki coefficient).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.completeCoefficient`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.completeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Take the supremum of supported Umegaki output-to-input ratios over every finite quantum reference and all joint density pairs with equal reference marginals and strictly positive finite input entropy. Adjoin zero to give the empty ratio set coefficient zero.

**Definition 1.2 (Conditional Umegaki coefficient).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.conditionalCoefficient`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.conditionalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Allow arbitrary supported joint density pairs and subtract the respective marginal divergences at input and output. Require a strictly positive finite input deficit. The actual output marginals equal the input marginals by trace preservation, and data processing makes every term finite on the admitted branch.

**Theorem 1.3 (Entropy controls the faithful endpoint tests).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.depolarized_endpointBound_completeCoefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.depolarized_endpointBound_completeCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Approximate every nonzero left-endpoint test of a genuinely output-depolarized channel with actual equal-marginal density pairs. Data processing bounds the depolarized ratio by the ratio for the original channel on the same pairs. The supremum then bounds the endpoint test, including the separate zero-form case.

**Theorem 1.4 (Contraction at the support boundary).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.supported_conditional_relativeEntropy_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.supported_conditional_relativeEntropy_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform endpoint bound on genuine output depolarizations contracts the supported conditional deficit for the original channel. At fixed output depolarization first remove common replacement noise at the input. Then remove output noise using each state's own reference marginal. On any joint matrix the replacement is the partial trace tensored with the normalized identity. For a density matrix these are exactly the entries of the product state of its reference marginal and the uniform state. The metric estimates use that same matrix formula on the output of N. The same CPTP map acts on both states in each step, supplying the upper bounds needed for the supported limits.

**Theorem 1.5 (Equality on the finite support branch).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.conditionalCoefficient_eq_completeCoefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.conditionalCoefficient_eq_completeCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For each finite CPTP channel the complete and conditional Umegaki coefficients coincide. This rules out the relative-entropy instance of the strict separation asked in the second bullet of §9 of Hirche, George, Nuradha and Wilde, arXiv:2608.27171v1. Definition 2, Eqs. (2.13) and (2.14), and Remark 2 determine the ratios and the positive finite denominator convention.

The equal-marginal ratios embed into the conditional ratios. The faithful endpoint approximation and ordered support limits give the reverse bound. Squared trace distance supplies the separate strict separation in FaithfulConditionalGap.result.

**Theorem 1.6 (Actual finite arithmetic inverse form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalInverse_channel_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalInverse_channel_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite joint base, a complex direction of zero partial trace, and 0 ≤ t ≤ 1, boundedness of the input quadratic tests implies boundedness at the actual amplified output. The output supremum is at most the complete entropy coefficient times the input supremum.

**Definition 1.7 (Arithmetic metric coefficient at t).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t in [0,1], take ratios over every finite reference, faithful correlated input bases and complex zero-partial-trace directions of positive input inverse form. Use the actual output variational form and adjoin zero before taking the supremum. The supported Moore–Penrose form is its exact output representation.

**Theorem 1.8 (Upper bound at each parameter).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t in the closed unit interval, the actual metric coefficient lies between zero and the complete Umegaki coefficient.

**Theorem 1.9 (Left endpoint and the metric supremum).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left-endpoint coefficient c₀ equals the complete coefficient ηᶜ, which equals the conditional coefficient ηΔ, which equals sup over 0 ≤ t ≤ 1 of cₜ. A comparison with output depolarizations makes c₀ a uniform endpoint bound and supplies the reverse entropy inequality.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.completeCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.conditionalCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.conditionalCoefficient_eq_completeCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.depolarized_endpointBound_completeCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.supported_conditional_relativeEntropy_contraction`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalInverse_channel_contraction`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient_bounds`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.variationalMetricCoefficient_chain`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiConditionalBKM](UmegakiConditionalBKM.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiFaithfulLowerRatio](UmegakiFaithfulLowerRatio.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiSupportedNoise](UmegakiSupportedNoise.md)
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/Recovery/QubitCenteredTransport](../Recovery/QubitCenteredTransport.md)
