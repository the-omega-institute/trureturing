# Sparse Kernel Rank

## Abstract

Infinite rational rank of the PPL binary kernel.

**Theorem 1.1 (Infinite rational kernel span).**

$$\neg \operatorname{FiniteDimensional}\left(\mathbb{Q}, \operatorname{span}\left(\mathbb{Q}, \operatorname{twoKernel}\left(\lambda n:\mathbb{N} \mapsto \operatorname{cast}\left(\operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right), \mathbb{Q}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.stronger_PPL_kernel_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational span of the binary kernel of period-doubling prefix palindromic length is infinite-dimensional. Evaluating the subsequences at the sparse upper blocks gives a matrix which becomes unit lower triangular after subtracting two separable terms. The evaluation size is arbitrary. The exact diagonal and off-diagonal values supply its entries. cast denotes natural-to-rational coercion.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.stronger_PPL_kernel_span`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/KernelSpan](KernelSpan.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseExactDiagonal](SparseExactDiagonal.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal](SparseExactOffDiagonal.md)
