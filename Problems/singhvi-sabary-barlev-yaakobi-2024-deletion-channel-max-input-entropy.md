---
slug: singhvi-sabary-barlev-yaakobi-2024-deletion-channel-max-input-entropy
bibkey: singhvi2025conditionalentropies
doi: 10.1109/TIT.2025.3581849
url: https://arxiv.org/abs/2407.10026v2
triage: theorem
motivation_gids:
  - D5/S3/Entropy/SinghviMaxInputEntropy.result
---

# Maximal input entropy for binary two-deletion and two-insertion channels

## Problem

Singhvi, Sabary, Bar-Lev and Yaakobi, *Conditional Entropies of k-Deletion/Insertion Channels*, arXiv:2407.10026v2, Section VII-A, ask:

> While we provide a complete characterization of the sequences that minimize input entropy, the precise identification of the sequences that maximize input entropy for the 2-deletion and 2-insertion channels is still unresolved. Determining these sequences and the associated maximal entropy values remains an important open direction.

Issue #19173 fixes the formal statement. For a received binary word, the posterior on uniformly transmitted inputs is proportional to the number of increasing index sets realizing the received word as a subsequence. Entropy is Shannon entropy in bits. The claim gives the two alternating families and their complements, the exact deletion and large insertion maxima, and the finite insertion cases of received lengths two, three and four.

### Statement echo

The Lean `claim` in `D5/S3/Entropy/SinghviMaxInputEntropy.lean` inlines the two posterior definitions, quantifies over the same finite binary words, uses the frozen embedding count and Shannon entropy, divides by `Real.log 2`, and states all seven clauses of the preregistration. The public `result : claim` is the settling declaration.

## Motivation

The source settles the minimizing sequences for two deletions but leaves the maximizing sequences and values open. Alternating words are proved here to maximize the input entropy for every positive deletion length and for insertion lengths at least five, with the exact exceptional small lengths recorded in the claim.

## Gap

The question is explicit in Section VII-A of arXiv:2407.10026v2 and was preregistered in issue #19173 before formalization. The bounded literature screen covered the source, its ITW predecessor arXiv:2202.03024, Atashpendar's thesis arXiv:2003.11663, the DOI, author searches and the phrases “deletion channel” with “input entropy” and “insertion channel” with entropy and alternating. No settlement was found in that scope. Completeness is `ASSUMED-UNVERIFIED`.

## Route

For a binary word with run lengths $r_1,\ldots,r_R$, classify the positive two-deletion multiplicities into contributions from two deletions in one run, from nonadjacent runs, and from components of adjacent run pairs joined through singleton runs. This gives the exact joint count distribution and the deletion run functional.

For deletion, strict convexity and a local shortening argument remove every run of length at least three. Jensen's inequality then shows that every remaining nonalternating run profile has strictly larger collision functional than the two alternating profiles. The exact alternating distribution gives the closed deletion value.

For insertion, grouping supersequence masks by run components gives lower bounds in terms of the number of excess runs. Strict scalar comparisons and Jensen's inequality prove the alternating minimizers of the collision functional for lengths at least five; the received lengths two, three and four are evaluated directly. The entropy ordering follows because, at fixed total mass, Shannon entropy is the negative normalized collision functional.

## Falsifier

The result would not settle the source question if the posterior used a different input distribution, if embeddings were counted without multiplicity of increasing index sets, if deletion and insertion lengths were interchanged, or if the theorem omitted the equality cases. A counterexample to any of the strict run comparisons or to one of the finite insertion cases would also falsify the stated settlement.

## Evidence

The settling module is `D5/S3/Entropy/SinghviMaxInputEntropy.lean`; its public declarations are `claim` and `result`, with `result : claim`. The supporting modules are `D5/S1/Words/TwoDeletionRunDecks.lean`, `D5/S1/Words/AlternatingTwoDeletionCounts.lean`, `D5/S1/Words/BinaryRunSupersequenceCounts.lean`, `D5/S3/Entropy/TwoDeletionRunEntropyBounds.lean` and `D5/S3/Entropy/TwoDeletionChannelEntropy.lean`.

The formalization reuses the frozen embedding and entropy owners. The supporting public escape witnesses are `collisionBlocks_realize`, `count_alt_two`, `jointWordSum_runs`, `run_coarse_insertion_bound` and `actual_run_deletion_lower`; the settling `result` is content and has admission basis `open-problem-resolution (#19173; Proved)`. The standard axiom closure is the repository's three permitted axioms; no additional axiom or `sorry` is used.

The preregistered experiment is in `the-omega-institute/trureturing-experiments`, commit `9c5a3fc3`, at `docs/reports/singhvi-sabary-barlev-yaakobi-2025-two-deletion-max-input-entropy/check.py`, SHA-256 `bc03924138dbcc4517b3f7f5228d69699ec19ee932d348728f425ed071d829e3`, exit code 0, with `RESULT PASS`. It exhaustively checked the two-deletion maximizers through length 12 and the two-insertion maximizers through length 16, including the closed forms and the run-count classification on all words through length 12.

## Triage

- **Proved:** `D5/S3/Entropy/SinghviMaxInputEntropy.result` establishes the unchanged issue #19173 claim.
- **Proved:** For every positive received length, the two-deletion maximizers are exactly an alternating word and its complement, with the stated closed value.
- **Proved:** For insertion lengths at least five, the maximizers are exactly the alternating word and its complement, with the stated closed value.
- **Proved:** At received lengths two, three and four, the finite maximizer descriptions in the claim hold.
- **Proved:** The exact joint run-count distribution and the strict run comparisons supply the mechanism used by the settling theorem.
- **Open:** The corresponding maximization questions for $k\ge3$ and for nonuniform inputs remain outside this settlement.
- **Open:** Exhaustive worldwide literature completeness and priority remain unverified.

## ASSUMED-UNVERIFIED

The literature screen is bounded and does not establish exhaustive worldwide novelty or priority. The experiment is evidence for finite ranges and regression checks; the universal conclusion is carried by the Lean kernel-checked theorem.
