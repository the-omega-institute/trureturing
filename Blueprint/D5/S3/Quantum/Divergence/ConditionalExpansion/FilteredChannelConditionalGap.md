# Conditional trace-gap lower bound for filtered channels

## Abstract

A finite channel obtained by positive filtering has a uniform lower bound on conditional trace gaps.

**Definition 1.1 (Filtered action).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filterAction`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filterAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite index types A and E, let e be the cardinality of E. Given G on A × E, the action sends each complex input matrix Z to √G ((Z ⊗ Iₑ)/e) √G.

**Theorem 1.2 (Exact CPTP realization).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.exists_filtered_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.exists_filtered_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Suppose E is nonempty, G is positive definite, and the partial trace of G over E divided by e is I on A. There exists a finite quantum channel N from A to A × E whose action equals the filtered action on every complex input matrix. Its Kraus operators are √G times the environment basis injections, divided by √e. Their adjoint products sum to I by the partial trace normalization.

**Theorem 1.3 (Hermitian gap under an inverse-marginal bound).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_conditional_trace_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_conditional_trace_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Assume the same positivity and normalization, and let N have the exact filtered action. Let L be the partial trace of G⁻¹ over E divided by e. If L ≤ kI in Loewner order for a real k > 0, the output conditional gap is at least 1/k times the input conditional gap. For a Hermitian joint input Z on R × A, the input gap is the trace of the negative part of Z minus that of its reference marginal. The output uses the amplified channel on Z and the same reference marginal. This holds for every finite R, including singular Z and mixed-sign reference marginals.

Lift the negative spectral projector of the reference marginal and take the normalized tensor extension by the environment identity. The derivative-free quadratic congruence bound applies with t = 1/k. Tracing out the environment bounds the inverse pairing by k times the input gap. Trace normalization preserves the reference projector term.

**Theorem 1.4 (Operator norm specialization).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_norm_trace_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_norm_trace_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

When A is also nonempty, L is positive definite and is bounded above by its operator norm times I. The lower bound on the output gap therefore has factor 1/‖L‖ for every finite reference and every Hermitian Z under the same filter hypotheses.

**Theorem 1.5 (Lower bound on conditional hockey-stick ratios).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_ratio_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_ratio_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For nonempty A and E and the same positive, normalized filter, every admissible conditional hockey-stick ratio of N is at least 1/‖L‖. Apply the Hermitian bound to γσ − ρ and divide by the strictly positive input gap. This applies to every real γ and either choice of the orthogonality flag. At γ = 1, when admissible ratios exist, it bounds the conditional trace-distance expansion infimum in Definition 3, Eq. (2.42). Attainment and sharpness of the recovery comparison remain outside these results.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.exists_filtered_channel`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filterAction`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_conditional_trace_gap`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_norm_trace_gap`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap.filtered_channel_ratio_lower_bound`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence](DerivativeFreeHarmonicCongruence.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiKernelContraction](../UmegakiKernelContraction.md)
