# Sparse Kernel Rank

## Abstract

Infinite rational rank of the PPL binary kernel.

**Definition 1.1 (The literal binary kernel).**

$$\forall A \in \operatorname{Type},\; \forall f \in \mathbb{N} \to A,\; \operatorname{twoKernel}\left(f\right) = \{g:\mathbb{N} \to A \mid \exists e \in \mathbb{N},\; \exists r \in \mathbb{N},\; r < 2^{e} \land g = n:\mathbb{N} \mapsto f\left(2^{e} \cdot n + r\right)\}$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.twoKernel` (`✓ std3`).

*Citation.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

This is the literal k = 2 case of the k-kernel definition in the FLP paper (Frid, Laborde and Peltomäki, On prefix palindromic length of automatic words). The binary kernel contains exactly the functions n mapped to f(2^e n+r), with e nonnegative and r strictly below 2^e. Its output carrier A is unrestricted.

**Theorem 1.2 (Infinite rational kernel span).**

$$\neg \operatorname{FiniteDimensional}\left(\mathbb{Q}, \operatorname{span}\left(\mathbb{Q}, \operatorname{twoKernel}\left(\lambda n:\mathbb{N} \mapsto \operatorname{cast}\left(\operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right), \mathbb{Q}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.stronger_PPL_kernel_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational span of the binary kernel of period-doubling prefix palindromic length is infinite-dimensional. Evaluating the subsequences at the sparse upper blocks gives a matrix which becomes unit lower triangular after subtracting two separable terms. The evaluation size is arbitrary. The exact diagonal and off-diagonal values supply its entries. cast denotes natural-to-rational coercion.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.stronger_PPL_kernel_span`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.twoKernel`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseExactDiagonal](SparseExactDiagonal.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal](SparseExactOffDiagonal.md)
