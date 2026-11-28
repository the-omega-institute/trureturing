# Binary testing and ordinary Petz under classical flag refinement

## Abstract

A common classical flag refinement preserves binary testing and the actual partial-trace Petz error and entropy loss.

For each parent flag, choose a finite child set and weights summing to one. Apply the same weights to both block families. The joint matrices are block diagonal on the retained space and the flag space. Taking the right partial trace sums the blocks, so each retained marginal is unchanged.

**Theorem 1.1 (The weighted testing norm is preserved).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_binary_testing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_binary_testing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two block families, any real coefficient p, and nonnegative normalized weights, the trace norm of p times the first joint matrix minus (1 − p) times the second is unchanged by refinement. The weighted difference refines block by block. The trace norm adds over direct sums, and each child contributes its weight times its parent's norm. For density matrices and p in [0, 1], the Helstrom formula gives equality of the optimal binary Bayes risks.

**Definition 1.2 (Ordinary Petz for the right partial trace).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTracePetz`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTracePetz` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a joint reference, sandwich the retained input by the inverse square root of the reference marginal. Tensor the result with the flag identity, then sandwich by the square root of the joint reference. The lift is the adjoint of the right partial trace for the Hilbert–Schmidt pairing. The formula gives the ordinary Petz map when the reference and its marginal are faithful. For positive definite reference blocks, a nonempty parent flag set ensures faithfulness of the retained marginal.

**Definition 1.3 (Petz recovery in each reference block).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.petzBlocks`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.petzBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a block diagonal reference, every output block uses the same retained inverse-square-root sandwich. Its outer factors are the square root of that block of the reference. Assembling these blocks gives the ordinary Petz output.

**Lemma 1.4 (Trace norm adds over flag blocks).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.traceNorm_joint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.traceNorm_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite family of square complex matrices S indexed by the flags, the trace norm of joint(S) equals the sum of the trace norms of its blocks.

**Lemma 1.5 (Petz recovery respects the flag blocks).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTracePetz_joint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTracePetz_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite reference blocks T and any retained input matrix X, partialTracePetz(joint(T), X) equals the joint matrix of petzBlocks(T, X).

**Theorem 1.6 (Petz recovery intertwines with refinement).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_ordinaryPetz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_ordinaryPetz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite reference blocks and strictly positive normalized weights, every retained input matrix has the same refined output whether one recovers against the refined reference or refines the recovered blocks. The marginal inverse square root is unchanged, while each of the two outer square roots contributes a factor equal to the square root of the child weight. The matrix identity also holds for empty flag sets.

**Theorem 1.7 (The actual trace-norm recovery error is preserved).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_petz_error`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_petz_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recover the actual right marginal of the input using the respective old or refined reference. For arbitrary input blocks, positive definite reference blocks and strictly positive normalized weights, the trace norm of the input joint matrix minus the recovered joint matrix is unchanged. The refined error matrix is obtained by applying the same weights to the blocks of the old error.

**Definition 1.8 (The finite trace-log expression).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.relativeEntropyOfMatrices`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.relativeEntropyOfMatrices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real trace of the input multiplied by its matrix logarithm minus the reference logarithm, with the difference formed before multiplying. For a positive semidefinite input and a faithful reference this is the Umegaki trace expression. Zero eigenvalues of the input contribute zero to its own logarithm term.

**Definition 1.9 (Loss across the actual right partial trace).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTraceEntropyLoss`

*Formalization.* `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTraceEntropyLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the trace-log expression for the two retained marginals from the trace-log expression for the two joint matrices.

**Theorem 1.10 (Both joint relative entropy and its partial-trace loss are preserved).**

Lean statement: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_entropy_loss`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_entropy_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume positive semidefinite input blocks, positive definite reference blocks and strictly positive normalized weights. The joint trace-log expression is unchanged, and the actual partial-trace loss is unchanged. On a child block, scaling both arguments by the same weight adds a logarithmic shift on their respective supports. Multiplication by the input kills its kernel, so these shifts cancel in the trace even for singular input blocks. The remaining term scales by the weight and sums to the original joint expression. Both marginal matrices agree before and after refinement.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTraceEntropyLoss`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTracePetz`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.partialTracePetz_joint`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.petzBlocks`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_binary_testing`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_entropy_loss`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_ordinaryPetz`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.refine_petz_error`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.relativeEntropyOfMatrices`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.traceNorm_joint`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinement](BKMFlagRefinement.md)
