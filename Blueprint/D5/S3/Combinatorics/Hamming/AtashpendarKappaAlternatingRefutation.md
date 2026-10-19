# Alternating words need not minimize positional autocorrelation

## Abstract

A period-six binary word has smaller positional autocorrelation than the alternating word at length 348.

Equation (11) of arXiv:1807.11609v1, p. 7, defines the natural-number coefficient κ²(x) = Σ₁≤ᵣ,ₛ≤ₘ C(r+s−2,r−1) C(2m−r−s,m−r) [[xᵣ=xₛ]]. Here positions are Fin m, with val taking values from zero to m minus one. Bool.true represents 1 and Bool.false represents 0. Natural subtraction truncates at zero; the binomial arguments are nonnegative for these positions. The percent operator is natural remainder. Each ordered pair of positions is counted once.

**Definition 1.1 (The alternating-minimizer conjecture).**

$$claim = (\forall (m: \mathbb{N}), 1 \le m \Rightarrow (\forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), (\sum_{r: \operatorname{Fin}\left(m\right)} \sum_{s: \operatorname{Fin}\left(m\right)} (\operatorname{if} (\operatorname{decide}\left(\operatorname{val}\left(r\right) \bmod 2 = 0\right): \operatorname{Bool}) = \operatorname{decide}\left(\operatorname{val}\left(s\right) \bmod 2 = 0\right) \operatorname{then} \operatorname{Nat}.\operatorname{choose}\left(\operatorname{val}\left(r\right) + \operatorname{val}\left(s\right), \operatorname{val}\left(r\right)\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(2 \cdot m - 2 - \operatorname{val}\left(r\right) - \operatorname{val}\left(s\right), m - 1 - \operatorname{val}\left(r\right)\right) \operatorname{else} 0)) \le (\sum_{r: \operatorname{Fin}\left(m\right)} \sum_{s: \operatorname{Fin}\left(m\right)} (\operatorname{if} \operatorname{x}\left(r\right) = \operatorname{x}\left(s\right) \operatorname{then} \operatorname{Nat}.\operatorname{choose}\left(\operatorname{val}\left(r\right) + \operatorname{val}\left(s\right), \operatorname{val}\left(r\right)\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(2 \cdot m - 2 - \operatorname{val}\left(r\right) - \operatorname{val}\left(s\right), m - 1 - \operatorname{val}\left(r\right)\right) \operatorname{else} 0))))$$

*Formalization.* `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.claim` (`✓ std3`).

*Citation.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

Conjecture IV.4, p. 7: “The alternating subsequence of length m, i.e., x = 1010..., minimizes the autocorrelation coefficient κ².” For every positive natural length m, the formula compares the coefficient of 1010... with that of every binary word x of length m. Its two sums are Equation (11), with the source positions shifted down by one. The first word has true at precisely the even zero-based positions.

**Theorem 1.2 (A strict counterexample at length 348).**

$$\neg (\forall (m: \mathbb{N}), 1 \le m \Rightarrow (\forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), (\sum_{r: \operatorname{Fin}\left(m\right)} \sum_{s: \operatorname{Fin}\left(m\right)} (\operatorname{if} (\operatorname{decide}\left(\operatorname{val}\left(r\right) \bmod 2 = 0\right): \operatorname{Bool}) = \operatorname{decide}\left(\operatorname{val}\left(s\right) \bmod 2 = 0\right) \operatorname{then} \operatorname{Nat}.\operatorname{choose}\left(\operatorname{val}\left(r\right) + \operatorname{val}\left(s\right), \operatorname{val}\left(r\right)\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(2 \cdot m - 2 - \operatorname{val}\left(r\right) - \operatorname{val}\left(s\right), m - 1 - \operatorname{val}\left(r\right)\right) \operatorname{else} 0)) \le (\sum_{r: \operatorname{Fin}\left(m\right)} \sum_{s: \operatorname{Fin}\left(m\right)} (\operatorname{if} \operatorname{x}\left(r\right) = \operatorname{x}\left(s\right) \operatorname{then} \operatorname{Nat}.\operatorname{choose}\left(\operatorname{val}\left(r\right) + \operatorname{val}\left(s\right), \operatorname{val}\left(r\right)\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(2 \cdot m - 2 - \operatorname{val}\left(r\right) - \operatorname{val}\left(s\right), m - 1 - \operatorname{val}\left(r\right)\right) \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/atashpendar-mestel-roscoe-ryan-2018-kappa-alternating-minimizer` (refuted) by `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"atashpendar-mestel-roscoe-ryan-2018-kappa-alternating-minimizer","declaration_gid":"D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

At length 348, the word (011001) repeated 58 times has strictly smaller coefficient than 1010.... The natural difference, alternating minus period-six, is 72205957507799609560655006349961851153741188979911147028434625522749530872921557830312745632696473970699075168094975823625414930530038291298408559098670303166362893884742404955920795949372113567213277960. A finite factorial table computes the two binomial factors. Each of the 348 row sums is checked for both words, in 29 groups of 12 rows, and their totals give this positive difference. The calculation proves the displayed negation. It does not determine the smallest counterexample length, the minimizers at other lengths, or an entropy ordering.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.result`
- Dependency: [D5/S3/Entropy/DeletionChannelEntropyOrdering](../../Entropy/DeletionChannelEntropyOrdering.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMCertificateData](../../Quantum/Entanglement/EJM/EJMCertificateData.md)
