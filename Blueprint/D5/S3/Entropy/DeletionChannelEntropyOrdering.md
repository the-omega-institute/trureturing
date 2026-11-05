# Finite Deletion-Channel Entropy Ordering

## Abstract

Positional autocorrelation does not determine the finite entropy order of binary deletion-channel outputs.

**Theorem 1.1 (embeddings_eq_count).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (x: (\operatorname{Fin} m) \to (\operatorname{Bool})), (\forall (y: (\operatorname{Fin} n) \to (\operatorname{Bool})), (\operatorname{embeddings} x y = \operatorname{scatteredCount} (\operatorname{List}.\operatorname{ofFn} x) (\operatorname{List}.\operatorname{ofFn} y)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings_eq_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

The formula relates a word's constant runs and its scattered-subword counts.

Binary strings of length k are functions Fin k to Bool, with false representing 0 and true representing 1. List.ofFn reads positions in increasing order. List.sublists counts index subsets with multiplicity: equal subwords from distinct masks remain separate. Natural subtraction is truncated at zero. The sum defining kappa2 uses zero-based positions, corresponding to the source's one-based Eq. (11). All binomial coefficients and embedding counts are natural numbers; the explicitly typed casts in entropyBits are real.

**Definition 1.2 (Embedding count).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \forall (y: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}), \operatorname{embeddings}\left(x, y\right) = \operatorname{List}.\operatorname{length}\left(\operatorname{List}.\operatorname{filter}\left((\operatorname{fun} (z: \operatorname{List}\left(\operatorname{Bool}\right)) \mapsto z = \operatorname{List}.\operatorname{ofFn}\left(x\right)), \operatorname{List}.\operatorname{sublists}\left(\operatorname{List}.\operatorname{ofFn}\left(y\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings` (`✓ std3`).

*Citation.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

Section III-A.f, p. 3: "Let ωx(y) denote the number of distinct ways that y can project to x:" The number of ways the word y deletes to x is counted by index subsequences. Distinct index subsequences are counted separately even when their letters agree.

**Definition 1.3 (Total embedding mass).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \operatorname{D5}.\operatorname{S3}.\operatorname{Arith}.\operatorname{FibonacciAtomic}.\operatorname{CommonPrediction}.\operatorname{Capacity}.\operatorname{pref}\left(n, m\right) = \operatorname{Nat}.\operatorname{choose}\left(n, m\right) \cdot 2^{n - m}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.pref` (`✓ std3`).

*Citation.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

The source's mu indexed by n and m is the binomial factor D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref(n,m). Equation (1), p. 4, gives this factor as C(n,m) times 2 to the power n minus m. For the lengths used in the comparison, m is positive and strictly less than n.

**Definition 1.4 (Posterior entropy in bits).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{entropyBits}\left(n, x\right) = \frac{\operatorname{D5}.\operatorname{S3}.\operatorname{Entropy}.\operatorname{MaxEntropy}.\operatorname{shannonEntropy}\left((\operatorname{fun} (y: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \mapsto \frac{(\operatorname{embeddings}\left(x, y\right): \mathbb{R})}{(\operatorname{D5}.\operatorname{S3}.\operatorname{Arith}.\operatorname{FibonacciAtomic}.\operatorname{CommonPrediction}.\operatorname{Capacity}.\operatorname{pref}\left(n, m\right): \mathbb{R})})\right)}{\operatorname{Real}.\operatorname{log}\left(2\right)}$$

*Formalization.* `D5/S3/Entropy/DeletionChannelEntropyOrdering.entropyBits` (`✓ std3`).

*Citation.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

Section III-A.f, p. 3: "Let ωx(y) denote the number of distinct ways that y can project to x:" The displayed expression counts the masks with y projected to x. The following sentence is: "we refer to the number of masks associated with a pair (y, x) as the weight of y, i.e., the number of times x can be embedded in y as a subsequence." Equation (3), p. 4, takes the base-two Shannon entropy of these counts divided by pref(n,m). The formula sums over all binary words; incompatible words contribute zero. D5.S3.Entropy.MaxEntropy.shannonEntropy sums Real.negMulLog, and division by Real.log 2 converts nats to bits.

**Definition 1.5 (Positional autocorrelation).**

$$\forall (m: \mathbb{N}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{kappa2}\left(x\right) = \sum_{r: \operatorname{Fin}\left(m\right)} \sum_{s: \operatorname{Fin}\left(m\right)} (\operatorname{if} \operatorname{x}\left(r\right) = \operatorname{x}\left(s\right) \operatorname{then} \operatorname{Nat}.\operatorname{choose}\left(\operatorname{val}\left(r\right) + \operatorname{val}\left(s\right), \operatorname{val}\left(r\right)\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(2 \cdot m - 2 - \operatorname{val}\left(r\right) - \operatorname{val}\left(s\right), m - 1 - \operatorname{val}\left(r\right)\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Entropy/DeletionChannelEntropyOrdering.kappa2` (`✓ std3`).

*Citation.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

Equation (11), p. 7, weights each equal pair of letters by two positional binomial coefficients. The variables r and s range over Fin m; val supplies their natural-number indices.

**Definition 1.6 (The proposed finite entropy order).**

$$claim = \forall (m: \mathbb{N}), \forall (n: \mathbb{N}), 1 \le m \Rightarrow m < n \Rightarrow \forall (u: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \forall (v: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{kappa2}\left(v\right) < \operatorname{kappa2}\left(u\right) \Rightarrow \operatorname{entropyBits}\left(n, u\right) \le \operatorname{entropyBits}\left(n, v\right)$$

*Formalization.* `D5/S3/Entropy/DeletionChannelEntropyOrdering.claim` (`✓ std3`).

*Citation.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

Section V, p. 10: "Beyond establishing this maximization, proving the entropy ordering of x strings determined by κ2(x) for finite n and m represents another open problem." Section IV-E.3, p. 10: "our numerical results indicate that κ2(x) predicts the entropy ordering perfectly in the finite length domain as well, i.e., for small and comparable fixed values of n and m. An example obtained from empirical data is presented in Table I to illustrate the correlation between Hn(x) and κ2(x) for n = 8 and m = 5." The formula expresses the order of Table I: strictly larger kappa2 implies no larger entropyBits. It compares any two words of the same positive length m at every input length n greater than m.

**Theorem 1.7 (The finite entropy order fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/DeletionChannelEntropyOrdering.result` (`✓ std3`). ∎

*Resolves.* `Problems/atashpendar-mestel-roscoe-ryan-2018-kappa2-entropy-ordering` (refuted) by `D5/S3/Entropy/DeletionChannelEntropyOrdering.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"atashpendar-mestel-roscoe-ryan-2018-kappa2-entropy-ordering","declaration_gid":"D5/S3/Entropy/DeletionChannelEntropyOrdering.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan (2018). *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*. URL: <https://arxiv.org/abs/1807.11609v1>.

*Commentary.*

At m = 5 and n = 8, the words 00100 and 01110 have kappa2 values 450 and 410. Their entropies have the reverse of the proposed order: entropyBits(8,01110) is strictly less than entropyBits(8,00100). Both embedding histograms have total mass 448. The sum of w log(w) is the logarithm of the integer product of w to the power w. A strict product comparison gives the strict entropy comparison, hence the negation of claim. This finite comparison leaves the source's asymptotic minimization theorem unchanged.

## An odd family with a half-bit entropy gap

For every integer r at least 1, set m = 2r + 1 and n = 2r + 2. The word x_r is 0 followed by 2r - 1 ones and then 0; y_r is r zeros, one 1, and r zeros. In native Fin coordinates, x_r(i) is true exactly when 0 < i.val < 2r, and y_r(i) is true exactly when i.val = r. List.ofFn gives runWord false [1, 2r - 1, 1] and runWord false [r, 1, r], respectively. These lists have length 2r + 1. Natural indices correspond to source positions i.val + 1; substitution in both binomial weights gives the source's one-based formula.

The source word and the increasing m-position mask are independent and uniform. Each mask-word pair has mass 1/(2^n C(n,m)). Summing precisely the masks that output x gives joint mass omega_x(y)/(2^n C(n,m)). The identity embeddings_eq_count and the fixed-length sublists count retain each index embedding separately, even when the selected letters coincide. The generic deletion_total in TwoDeletionChannelEntropy gives total mass C(n,m) times 2^(n-m). Conditioning this joint law gives the exact posterior used by entropyBits. The inherited definitions include the empty pattern and all zero-weight words; zero entropy summands remain zero.

Write f(t) = t log_2(t), with f(0) = 0. For positive consecutive run lengths a_1 through a_s, BinaryRunSupersequenceCounts.oneWordSum_runs applied to f gives the sum of weight times log_2(weight) as the sum of f(a_i + 1): its remaining term is a multiple of f(1) = 0. The generic entropy_eq_log_sub_phi in TwoDeletionChannelEntropy then gives the single-deletion run formula, with normalizer 2(m + 1). Thus the two displayed run lists give the following exact bit gap.

$$
\operatorname{entropyBits}\left(2 \cdot r + 2, y_{r}\right) - \operatorname{entropyBits}\left(2 \cdot r + 2, x_{r}\right) = \frac{\operatorname{f}\left(2 \cdot r\right) + \operatorname{f}\left(2\right) - 2 \cdot \operatorname{f}\left(r + 1\right)}{4 \cdot (r + 1)}
$$

For r at least 2 the numerator is strictly positive. Indeed, strict convexity of t log(t) at the distinct positive points 2 and 2r gives f(2) + f(2r) > 2 f(r + 1), since log(2) is positive. The denominator 4(r + 1) is positive.

For autocorrelation, let M be the source's positional weight matrix, B = C(2r,r), C = C(4r,2r), and S = C(4r + 1,2r). The coefficient identity PowerSeries.mk_one_pow_eq_mk_choose_add, multiplication of powers, and coefficient convolution show that each row sum of M is S. The matrix is symmetric. For a word, the equal-letter sum is the total matrix sum minus twice the zero-one cross sum. The endpoint entries are C, C, 1, 1; the middle diagonal entry is B squared. Consequently the cross sums of x_r and y_r are 2(S - C - 1) and S - B squared. Using S = (4r + 1) C / (2r + 1) gives the exact difference below. Both kappa2 values are cast to the reals before subtraction.

$$
(\operatorname{kappa2}\left(y_{r}\right): \mathbb{R}) - (\operatorname{kappa2}\left(x_{r}\right): \mathbb{R}) = 2 \cdot (\operatorname{Nat}.\operatorname{choose}\left(2 \cdot r, r\right)^{2} - \frac{\operatorname{Nat}.\operatorname{choose}\left(4 \cdot r, 2 \cdot r\right)}{2 \cdot r + 1} - 2)
$$

Its sign can also be read from the pinned binomial square-sum and central-maximum identities. They give C at most 2 + (2r - 1) B squared: the two endpoint terms are 1, and each of the other 2r - 1 terms is at most B squared. Also B is at least 2r. For r at least 2 this implies B squared > 2r + 2, so B squared - C/(2r + 1) - 2 is at least 2(B squared - 2r - 2)/(2r + 1), which is strictly positive. Thus the autocorrelation and entropy comparisons hold simultaneously for these same words.

Logarithm multiplication and division rules rewrite the same entropy gap as

$$
\operatorname{entropyBits}\left(2 \cdot r + 2, y_{r}\right) - \operatorname{entropyBits}\left(2 \cdot r + 2, x_{r}\right) = \frac{1}{2} - \frac{\operatorname{Real}.\operatorname{logb}\left(2, r\right)}{2 \cdot (r + 1)} - \frac{1}{2} \cdot \operatorname{Real}.\operatorname{logb}\left(2, 1 + \frac{1}{r}\right)
$$

Along the integer family r tending to infinity, log_2(r)/(2(r + 1)) tends to zero by Real.tendsto_pow_logb_div_mul_add_atTop, and log_2(1 + 1/r) tends to zero by continuity at 1. Hence the entropy gap tends to one half bit. At r = 1 both words are 010 and both differences are zero; r = 0 is outside the family. This application concerns one deletion with both lengths growing together. It does not imply a capacity statement or alter the fixed-m, n tending to infinity regime.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.pref`
- Truth anchor: `D5/S3/Entropy/DeletionChannelEntropyOrdering.claim`
- Truth anchor: `D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings`
- Truth anchor: `D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings_eq_count`
- Truth anchor: `D5/S3/Entropy/DeletionChannelEntropyOrdering.entropyBits`
- Truth anchor: `D5/S3/Entropy/DeletionChannelEntropyOrdering.kappa2`
- Truth anchor: `D5/S3/Entropy/DeletionChannelEntropyOrdering.result`
- Dependency: [D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance](../../S0/Certificates/Hypergraphs/OrientationEntropyBalance.md)
- Dependency: [D5/S0/Tower/DBonacci/TerminalSampling](../../S0/Tower/DBonacci/TerminalSampling.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore](../../S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](../../S1/Words/Complexity/VivionBinomialConverseFails.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts](../Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
