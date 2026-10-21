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
