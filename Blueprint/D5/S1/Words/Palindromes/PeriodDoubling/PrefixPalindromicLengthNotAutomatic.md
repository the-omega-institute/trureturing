# Period-Doubling PPL-Difference Is Not Automatic

## Abstract

The PPL-difference of the period-doubling word has an infinite binary kernel.

**Definition 1.1 (Conjecture 17).**

$$claim = \left(\neg \operatorname{Finite}\left(\operatorname{twoKernel}\left(\lambda n:\mathbb{N} \mapsto \operatorname{cast}\left(\operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n + 1\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right), \mathbb{Z}\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.claim` (`✓ std3`).

*Citation.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

Frid, Laborde and Peltomäki, On prefix palindromic length of automatic words, arXiv:2009.02934v2, page 13, Conjecture 17: The sequence $d_{pd}$ of the period-doubling word $\mathbf{u}_{\mathrm{pd}}$ is not $2$-automatic, and so the prefix palindromic length $\left(\operatorname{PPL}_{pd}\right)\left(n\right)$ of $\mathbf{u}_{\mathrm{pd}}$ is not $2$-regular.

The alphabet uses false for a and true for b, and the substitution is a to ab and b to aa. PL minimizes the number of nonempty palindrome factors of the prefix of length n, with value zero on the empty prefix. The integer difference is PPL(n+1) minus PPL(n), for n at least zero. twoKernel includes every address (e,r) with e natural and r less than 2^e. Infinitude of this kernel is the stated non-automaticity criterion. cast records natural-to-integer coercion.

**Theorem 1.2 (Infinite difference kernel).**

$$\neg \operatorname{Finite}\left(\operatorname{twoKernel}\left(\lambda n:\mathbb{N} \mapsto \operatorname{cast}\left(\operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n + 1\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right), \mathbb{Z}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact sparse-family evaluations force unbounded rational rank of the PPL kernel. A finite difference kernel would force a finite-dimensional PPL kernel span by residue-block telescoping. This contradicts the rank bound and proves the displayed claim without hypotheses. The same rank argument proves the stronger failure of 2-regularity through infinite dimension of the rational kernel span.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.claim`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank](SparseKernelRank.md)
