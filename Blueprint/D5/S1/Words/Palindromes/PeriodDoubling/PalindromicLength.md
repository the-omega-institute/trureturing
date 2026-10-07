# Palindromic Length and Suffix Cuts

## Abstract

Optimal suffix cuts give the exact minimum and transfer cut potentials to lower bounds.

**Theorem 1.1 (An optimal final suffix).**

$$\forall A \in \operatorname{Type},\; \forall w \in \operatorname{List}\left(A\right),\; w \ne [] \Rightarrow \left(\exists j \in \mathbb{N},\; \left(j < \operatorname{length}\left(w\right) \land \operatorname{Palindrome}\left(\operatorname{drop}\left(j, w\right)\right)\right) \land \operatorname{PL}\left(w\right) = \operatorname{PL}\left(\operatorname{take}\left(j, w\right)\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength.optimal_suffix_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

PL and PalFactors are the canonical declarations from FridPrefix/PalindromicLength. An optimal factorization has a nonempty last factor. Its preceding length is the cut j. Replacing its preceding factorization by an optimal one proves the exact equality, rather than only an upper bound.

**Theorem 1.2 (Potentials bound the true minimum).**

$$\forall A \in \operatorname{Type},\; \forall w \in \operatorname{List}\left(A\right),\; \forall B \in \mathbb{N} \to \mathbb{N},\; \left(B\left(0\right) = 0 \land \left(\forall n \in \mathbb{N},\; n \le \operatorname{length}\left(w\right) \Rightarrow \left(\forall j \in \mathbb{N},\; \left(j < n \land \operatorname{Palindrome}\left(\operatorname{drop}\left(j, \operatorname{take}\left(n, w\right)\right)\right)\right) \Rightarrow B\left(n\right) \le B\left(j\right) + 1\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; n \le \operatorname{length}\left(w\right) \Rightarrow B\left(n\right) \le \operatorname{PL}\left(\operatorname{take}\left(n, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength.suffix_cut_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna E. Frid, Enzo Laborde, and Jarkko Peltomäki (2021). *On prefix palindromic length of automatic words*. DOI: [10.1016/j.tcs.2021.08.016](https://doi.org/10.1016/j.tcs.2021.08.016). URL: <https://arxiv.org/abs/2009.02934v2>.

*Commentary.*

A natural-valued potential starting at zero and decreasing by at most one on every palindromic suffix cut bounds the true minimum. Strong induction uses an optimal last suffix at each nonempty prefix.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength.optimal_suffix_cut`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PalindromicLength.suffix_cut_lower_bound`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/PalindromicLength](../FridPrefix/PalindromicLength.md)
