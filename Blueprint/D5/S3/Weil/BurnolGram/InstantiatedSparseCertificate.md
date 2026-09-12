# Instantiated Sparse Certificate

## Abstract

A supplied finite frame yields an instantiated sparse negative Weil certificate with proved geometry, cutoff, integer budget, depth, support and margin.

**Theorem 1.1 (Quantitative existence with the arithmetic premises discharged).**

Lean statement: `D5/S3/Weil/BurnolGram/InstantiatedSparseCertificate.exists_instantiated_sparse_negative_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/InstantiatedSparseCertificate.exists_instantiated_sparse_negative_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix R as the maximum of five and the sum of node norms before choosing either separation gap. Choose sigma from the distinct node squares, form sparsePacketExceptions at this fixed radius and gap, and only then choose tau. Nonnegative interpolation jet budgets give U at least R plus one, hence at least six. Thus T equals five satisfies the cutoff. Choose a natural c above the resulting real budget using exists_nat_ge. With den, p and q all equal to one, the finite-data theorem gives margin three at every N at least rationalQuarterDepth c 1 1 1, together with the support bound, positive definiteness of the negated actual full Gram and negative index equal to the cardinality of the frame index type.

WeilFullGramInertia.exists_actual_full_weil_gram_with_exact_negative_index already proves qualitative existence from the frame alone, including injective synthesis and exact inertia, with no remainder or arithmetic hypothesis. This companion supplies the quantitative depth, support radius and margin non-vacuously and retains all three geometric bounds.

This does not produce a frame. The offLine field requires an actual off-critical-line zero for each indexed orbit; producing a nonempty frame would itself be an RH counterexample. Everything is conditional on a supplied frame, and the index type may be empty. Finite existence is not numerical certification: the sparse coefficient bound grows like (1 + U squared) to the exception count, and the derivative bound grows with the node count plus the exception count. Tiny separation or many exceptions make these enormous; existence does not assert a usable size. The zero enumeration is chosen classically, with no executable enumeration with certified rational enclosures here.

## References

- Truth anchor: `D5/S3/Weil/BurnolGram/InstantiatedSparseCertificate.exists_instantiated_sparse_negative_certificate`
- Dependency: [D5/S3/Weil/BurnolGram/FrameSeparationParameters](FrameSeparationParameters.md)
