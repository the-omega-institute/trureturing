---
bibkey: singhvi2025conditionalentropies
authors: S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi
year: 2025
title: "Conditional Entropies of k-Deletion/Insertion Channels"
doi: 10.1109/TIT.2025.3581849
url: https://arxiv.org/abs/2407.10026v2
claim: "Section VII-A asks for the maximizing words and maximal input entropies of the binary two-deletion and two-insertion channels."
strata_touched:
  - D5/S1/Words/TwoDeletionRunDecks
  - D5/S3/Entropy/AlternatingTwoDeletionCounts
  - D5/S3/Entropy/BinaryRunSupersequenceCounts
  - D5/S3/Entropy/TwoDeletionRunEntropyBounds
  - D5/S3/Entropy/TwoDeletionChannelEntropy
  - D5/S3/Entropy/SinghviMaxInputEntropy
license: citation-only
triage: anchor
---

# Conditional Entropies of k-Deletion/Insertion Channels

## Verified locator

DOI: 10.1109/TIT.2025.3581849

Source: https://arxiv.org/abs/2407.10026v2

The source is arXiv:2407.10026v2; the journal version is IEEE Transactions on Information Theory 71(9), 6503–6516.

## Source question

Section VII-A, PDF p. 16:

> Maximal Input Entropy for k = 2. While we provide a complete characterization of the sequences that minimize input entropy, the precise identification of the sequences that maximize input entropy for the 2-deletion and 2-insertion channels is still unresolved. Determining these sequences and the associated maximal entropy values remains an important open direction.

The input distribution is uniform. Words in the formalization are functions from `Fin m` to `Bool`, with `false` representing 0. Embeddings count index subsets with multiplicity. The insertion indexing uses received length `m + 2` and input length `m`. Entropy is measured in bits.

## Scope

The question concerns input entropy. The two-deletion and two-insertion cases use different posterior sample spaces. The higher-deletion and nonuniform questions in Section VII-A are separate questions.

## Definitions

Section III, PDF p. 3:

> In this paper, we study the conditional entropies under uniform transmission.

> The embedding number of y in x, denoted by ωy (x), is defined as the number of distinct occurrences of y as a subsequence of x.

The source counts distinct increasing index sets, including when equal symbols give the same subsequence. Its example `x = 11220`, `y = 120` has embedding number 4.

Section II, PDF p. 2:

> Formally, for an input x ∈ Xⁿ, we refer to H(Y|X₁ⁿ = x) as the output entropy of the channel and for an output y ∈ Y*, H(X₁ⁿ|Y = y) is the input entropy of the channel.

Section III, PDF p. 4:

> The equivalent values and notations are defined similarly for the k-insertion channel, k-Ins.

The posterior definitions normalize embedding multiplicities over all binary input words. The entropy definitions apply Shannon entropy to those posteriors and divide the natural-logarithm value by `Real.log 2`. Section IV, PDF p. 5, Lemmas 2 and 3 give the corresponding embedding-count expressions.
