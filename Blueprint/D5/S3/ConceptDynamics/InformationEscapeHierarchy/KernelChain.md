# Generated-Kernel Chains

## Abstract

Classified generator schedules yield disjoint, telescoping escape decompositions.

**Definition 1.1 (Generator step classification).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.GeneratorStepClass`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.GeneratorStepClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each scheduled addition is certified either as a strict edge or as an extensional stutter.

**Definition 1.2 (Generator schedule).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.GeneratorSchedule`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.GeneratorSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete bijective ordering records every catalog addition, its node sequence, endpoints, and classification.

**Definition 1.3 (Strict kernel chain).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.StrictKernelChain`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.StrictKernelChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stutter-free path retains a strict generator-step certificate at every adjacency.

**Definition 1.4 (Strict subsequence).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Deleting classified stutters produces a strict kernel chain while preserving the path endpoints.

**Theorem 1.5 (Strict subsequences preserve the first node).**

$$\operatorname{node}(\operatorname{strictSubsequence}(A), 0) = \operatorname{node}(A, 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence_node_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.6 (Strict subsequences preserve the terminal node).**

$$\operatorname{node}(\operatorname{strictSubsequence}(A), \operatorname{last}(\operatorname{strictSubsequence}(A))) = \operatorname{node}(A, \operatorname{last}(A)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence_node_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.7 (Retained labels come from the schedule).**

$$\operatorname{added}(\operatorname{strictSubsequence}(A), r) \in \operatorname{image}(\operatorname{added}(A), \operatorname{univ}()).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence_added_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Remark 1.8 (Schedule increment rate).**

$$
\operatorname{incrementRate}(A, r) = \frac{\operatorname{incrementCount}(A, r)}{\operatorname{escapeDenominator}(A)}.
$$

*Source.* Repository-derived.

*Commentary.*

GeneratorSchedule.incrementRate uses the canonical arena escape denominator.

**Remark 1.9 (Strict-chain increment rate).**

$$
\operatorname{incrementRate}(K, r) = \frac{\operatorname{incrementCount}(K, r)}{\operatorname{escapeDenominator}(A)}.
$$

*Source.* Repository-derived.

*Commentary.*

StrictKernelChain.incrementRate uses the canonical arena escape denominator.

**Theorem 1.10 (Collapsed increments are empty).**

$$\operatorname{node}(A, \operatorname{castSucc}(r)) = \operatorname{node}(A, \operatorname{succ}(r)) \Rightarrow \operatorname{increment}(A, r) = \emptyset.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.collapsed_increment_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.11 (Chain increments are pairwise disjoint).**

$$\forall r, s, r \neq s \implies \operatorname{Disjoint}(\operatorname{increment}(A, r), \operatorname{increment}(A, s)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_increment_pairwise_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.12 (Increment union is terminal escape loss).**

$$\operatorname{biUnion}(\operatorname{univ}(), \operatorname{increment}(A)) = \operatorname{sdiff}(\operatorname{escapeAt}(\operatorname{node}(A, 0)), \operatorname{escapeAt}(\operatorname{node}(A, \operatorname{last}(A)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_increment_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.13 (Increment counts telescope).**

$$\operatorname{sum}(\operatorname{incrementCount}(A)) + \operatorname{card}(\operatorname{escapeAt}(\operatorname{node}(A, \operatorname{last}(A)))) = \operatorname{card}(\operatorname{escapeAt}(\operatorname{node}(A, 0))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_count_telescopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.14 (Increment rates telescope).**

$$\operatorname{sum}(\operatorname{incrementRate}(A)) + \operatorname{escapeRate}(\operatorname{node}(A, \operatorname{last}(A))) = \operatorname{escapeRate}(\operatorname{node}(A, 0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_rate_telescopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.15 (A strict-chain terminal is its generated union).**

$$\operatorname{node}(A, 0) = \operatorname{generatedKernel}(C, T) \Rightarrow \operatorname{node}(A, \operatorname{last}(A)) = \operatorname{generatedKernel}(C, \operatorname{union}(T, \operatorname{image}(\operatorname{added}(A)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strict_chain_terminal_eq_generatedKernel_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.16 (Strict-chain terminals are order independent).**

$$\left(\left(\operatorname{node}(A, 0) = \operatorname{generatedKernel}(C, T) \land \operatorname{node}(B, 0) = \operatorname{generatedKernel}(C, T)\right) \land \operatorname{image}(\operatorname{added}(A)) = \operatorname{image}(\operatorname{added}(B))\right) \Rightarrow \operatorname{node}(A, \operatorname{last}(A)) = \operatorname{node}(B, \operatorname{last}(B)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.terminal_order_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.17 (Full-schedule terminals are order independent).**

$$\operatorname{node}(A, \operatorname{last}(A)) = \operatorname{node}(B, \operatorname{last}(B)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.full_schedule_terminal_order_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.18 (A full schedule ends at the full kernel).**

$$\operatorname{node}(A, \operatorname{last}(A)) = \operatorname{generatedKernel}(C, \operatorname{fullIndexSet}(C)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.schedule_terminal_eq_generatedKernel_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

**Theorem 1.19 (The leave-one-out last step is unique capture).**

$$\left(\operatorname{PositiveLength}(A) \land \operatorname{node}(A, \operatorname{penultimate}(A)) = \operatorname{generatedKernel}(C, \operatorname{without}(C, i))\right) \Rightarrow \operatorname{increment}(A, \operatorname{last}(A)) = \operatorname{uniqueCapturePairs}(C, i).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.last_step_eq_uniqueCapture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate follows from classified generator steps and finite escape-set algebra.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.GeneratorSchedule`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.GeneratorStepClass`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.StrictKernelChain`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_count_telescopes`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_increment_pairwise_disjoint`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_increment_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.chain_rate_telescopes`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.collapsed_increment_eq_empty`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.full_schedule_terminal_order_independent`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.last_step_eq_uniqueCapture`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.schedule_terminal_eq_generatedKernel_full`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence_added_mem`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence_node_last`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strictSubsequence_node_zero`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.strict_chain_terminal_eq_generatedKernel_union`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.terminal_order_independent`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel](GeneratedKernel.md)
