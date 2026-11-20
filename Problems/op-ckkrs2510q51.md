---
slug: op-ckkrs2510q51
bibkey: chen2025lowautomaticcomplexity
doi: 10.48550/arXiv.2510.07696
url: https://arxiv.org/abs/2510.07696v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound.result
---

# Arbitrary-alphabet circuit lower bounds for low automatic complexity

## Problem

Chen, Kjos-Hanssen, Koswara, Richter and Stephan ask in Question 5.1 of *Languages of Words of Low Automatic Complexity Are Hard to Compute*:

> Do the results from Theorem 4.9 apply to arbitrary alphabets using the definition of ⊕SAC⁰ given in Definition 4.4?

The conference version asks the same question as Question 47 on p. 24:17. Theorem 4.9 excludes both the low-complexity language and its complement for alphabets of prime size. The conventions in [preregistration #26742](https://github.com/the-omega-institute/trureturing/issues/26742) give two arbitrary-alphabet interpretations. [arXiv v1](https://arxiv.org/abs/2510.07696v1) · [FSTTCS 2025](https://doi.org/10.4230/LIPIcs.FSTTCS.2025.24)

### Statement echo

| Source clause or preregistered convention | Lean counterpart | Scope |
| --- | --- | --- |
| Arbitrary finite alphabet $\Sigma$ with at least two letters | `claim` quantifies an alphabet type, its `Fintype` instance and its cardinality lower bound | All finite alphabets of the stated cardinality |
| Exact acceptance in Definition 1.1 | `exactlyAccepts` requires acceptance of the word and rules out every distinct same-length accepted word | Accepting paths may be multiple |
| Minimum state count | `realizesStateCount` uses an epsilon-free NFA with a singleton start set. `A_Ne` takes the infimum of the feasible finite counts | `complexityTotalProof` proves finite attainment for every word, including the empty word |
| Strict threshold $A_{Ne}(w)<q\lvert w\rvert$ | `Lq`, with the rational binders $0<q<1/2$ in `claim` | Length counts letters |
| Definition 4.4 fixes a circuit family with constant depth, bounded AND fan-in, arbitrary XOR fan-in and negative literals | `bounded` and `booleanRecognizable`, with uniform bounds outside the length quantifier and a circuit chosen before its input | Finite circuits, unrestricted size and no uniformity requirement. The layer assignment certifies acyclicity |
| Arithmetic interpretation in Definition 4.5 | `arithmeticRecognizable` uses evaluation in $\mathbb F_p$ with addition, multiplication and negatives $1-X_i$. `claim` quantifies prime $p$ and injective alphabet maps | Correctness on the alphabet grid. Constant gates include the values of empty sums and products |
| Original Boolean interpretation on arbitrary alphabets | `booleanRecognizable` and the width and injectivity binders of `claim` | Every fixed injective encoding into $t$ bits per letter. Correctness applies to valid blocks |
| Both conclusions of Theorem 4.9 | Two nonrecognition conjuncts in each of the arithmetic and Boolean branches of `claim` | Both $L_q$ and $\Sigma^*\setminus L_q$ |
| Added finiteness and attainment conjunct | `complexityTotal` | Discharges the minimum's existence without an extra hypothesis |

## Motivation

The Proved settling declaration is `D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound.result`. Its admission basis is `open-problem-resolution (#26742; Proved)`. The supporting `ExactNFACircuitInfrastructure` module uses the `gridSupportBound` escape witness. Both modules have generality `G` and utility `none`.

## Gap

The literature screen in #26742 found no affirmative arbitrary-alphabet circuit theorem or counterexample in the inspected arXiv full texts, citation and author searches, formalization catalogues and repository sources. Kjos-Hanssen and Rivera Petit, arXiv:2608.22271, address Question 5.2 and treat alphabet invariance in §6. Citation-provider gaps, unread manuscripts and incomplete author disambiguation leave the literature screen `ASSUMED-UNVERIFIED`. [Related paper](https://arxiv.org/abs/2608.22271)

## Route

The settling proof obtains sparse nonempty sections by bounding repeated factors. Acceptance of a constant word by a one-state automaton supplies nonemptiness. A bound on sequences of states along an accepting path implies that a sufficiently low state count forces a repeated factor. Deleting the later occurrence gives an injection for each fixed pair of factor positions, including overlaps, and counting the pairs bounds the section size.

The supporting module represents each circuit by a polynomial and bounds its total degree by $\max(1,b)^h$ when depth is bounded by $h$ and multiplication fan-in by $b$. Reduction on the grid and induction on the leading coefficient show that nonempty evaluation support occupies at least the fraction $r^{-D}$ on an $r$-letter grid for degree bound $D$. This is an Alon–Füredi type estimate. For complement recognition, the transformation $1-P^{p-1}$ makes the support equal to the zeros of $P$ on the prime-field grid. In the Boolean case, two distinct letters give affine substitutions in the block coordinates, and injective relabelling preserves exact automatic complexity. [Finite-grid literature](https://arxiv.org/abs/1508.06020v2)

## Falsifier

A recognizer family with the stated bounds, encoding and input correctness for either language would contradict `result`. A family whose fan-in or depth grows with word length falls outside these bounds.

## Evidence

The library record is `Library/PermutationPatterns/chen2025lowautomaticcomplexity.md`. The exact statement and its source acknowledgement appear in the settling Blueprint. The escape audit is unfinished. The original-source realization bridges and family variation, sensitivity and dependence evidence are missing for the nine public theorem targets. [Audit issue #30628](https://github.com/the-omega-institute/trureturing/issues/30628)

### Experiment

At the pinned experiments revision, `python3 docs/reports/chen-et-al-2510.07696-question-5.1-arbitrary-alphabet-circuits/check.py` exited 0 with `ALL_CHECKS_OK`. The script SHA-256 is `b1e88c6db3cbf86a3956dac11fd8e62536b757b3cabf59b65e89f4e2d285204c`. [Experiment directory at commit 8e43b321f87806b621faaf52f16659265c7fc2df](https://github.com/the-omega-institute/trureturing-experiments/tree/8e43b321f87806b621faaf52f16659265c7fc2df/docs/reports/chen-et-al-2510.07696-question-5.1-arbitrary-alphabet-circuits)

## Triage

1. **Core mechanism (proved, kernel-checked).** In `ExactNFACircuitInfrastructure`, `circuitPolynomialDegreeLe`, `gridSupportBound` and `sparsePolynomialObstruction` give the uniform-degree bound, positive support fraction and its contradiction with finite-scale sparsity. `complementTransform` gives the support identity for $1-P^{p-1}$ used by the complement results.
2. **Density mechanism (proved, kernel-checked).** In the settling module, `noRepeatsStateBound` gives $\lvert w\rvert+1\le 2k+m^2$ for an exact $k$-state realization with no repeated factor of positive length $m$. `lowImpliesRepeat` forces a repeat when $m^2\le(1-2q)\lvert w\rvert$. `repeatedCount` bounds the count of repeated-factor words at length $n$ by $(n+1)^2r^{n-m}$. `lowLanguageSparse` supplies the finite-scale sparsity and nonemptiness used by `result`.
3. **Alphabets and encodings (proved, kernel-checked).** `ExactNFACircuitInfrastructure.ANeMap` and `memLqMapIff` transport complexity and membership under any injective relabelling. `blockSubstitutionEval` and `blockSubstitutionDegree` give evaluation preservation and degree control for two encoded letters. The correctness premise of `booleanPolynomialFamily` ranges over valid encodings.
4. **Extent (proved, kernel-checked).** `ExactNFACircuitInfrastructure.gridSupportBound` works over every field, and `circuitPolynomialEval` and `circuitPolynomialDegreeLe` together apply over nontrivial commutative rings. The settling module's `noRepeatsStateBound` needs no finite-alphabet hypothesis. The arithmetic branch of the complete `result` uses prime fields.
5. **Finite checks (computed).** The pinned experiment above checked 411 cyclic-NFA witnesses at word lengths $1$ through $3$, alphabet sizes $2$ through $4$ and $q\in\{1/4,1/3,2/5\}$. It checked 25,612 polynomial/grid pairs with 25,051 nonempty supports for all eligible grids in ten printed dimension and degree cases over $\mathbb F_2$, $\mathbb F_3$ and $\mathbb F_5$. It also checked 620 binary-word relabelling comparisons at lengths $0$ through $4$ in ambient alphabets of sizes $2$ through $4$, and 70 ordered distinct Boolean codeword pairs of widths $1$ through $3$.
6. **Surviving neighbours (open).** The settlement leaves the endpoint $q=1/2$, growing depth or multiplication fan-in, and a separate full-density-limit Lean theorem open.

### What the settlement shows

**Proved in Lean.** At each fixed degree bound, a nonempty section of $L_q$ is too sparse to be that polynomial's support. This suffices for the four lower bounds in `result`, including alphabets whose cardinality is composite and encodings whose image omits field elements or bit blocks. The source's prime-cardinality theorem is covered by the arithmetic specialization. The proof supplies the sparse sections directly and does not assume the source's Corollary 2.10. The classical grid estimate, finite-field complement transform and alphabet invariance have prior mathematical treatments. The scope of the computed checks and the open neighbours is given in items 5 and 6.

## ASSUMED-UNVERIFIED

The literature screen establishes no priority or complete census of subsequent results. Its coverage and known limits are recorded in [preregistration #26742](https://github.com/the-omega-institute/trureturing/issues/26742).
