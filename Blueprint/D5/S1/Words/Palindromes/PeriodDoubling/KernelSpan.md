# Rational Spans of Binary Kernels

## Abstract

The binary kernel records every power-of-two residue subsequence.

**Definition 1.1 (The literal binary kernel).**

$$\forall A \in \operatorname{Type},\; \forall f \in \mathbb{N} \to A,\; \operatorname{twoKernel}\left(f\right) = \{g:\mathbb{N} \to A \mid \exists e \in \mathbb{N},\; \exists r \in \mathbb{N},\; r < 2^{e} \land g = n:\mathbb{N} \mapsto f\left(2^{e} \cdot n + r\right)\}$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/KernelSpan.twoKernel` (`✓ std3`).

*Citation.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

This is the literal k = 2 case of the k-kernel definition in the FLP paper (Frid, Laborde and Peltomäki, On prefix palindromic length of automatic words). The binary kernel contains exactly the functions n mapped to f(2^e n+r), with e nonnegative and r strictly below 2^e. Its output carrier A is unrestricted.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/KernelSpan.twoKernel`
