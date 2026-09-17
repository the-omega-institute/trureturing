---
bibkey: iliopoulos2017commutative
authors: "Fotis Iliopoulos"
year: 2017
title: "Commutative Algorithms Approximate the LLL-distribution"
doi: 10.48550/arXiv.1704.02796
url: https://arxiv.org/abs/1704.02796
claim: "Commutative resampling algorithms satisfying the stated cluster-expansion or Shearer condition have bounded expected flaw counts and query probabilities."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Commutative resampling and its required hypotheses

The inspected version is [v6](https://arxiv.org/html/1704.02796v6), dated
8 June 2019; first submission 10 April 2017. Checked 16 September 2026.
Section 2.2 defines causality and charges, Definition 2.1 requires a
probability-preserving injective swap, and Theorem 3.2(1) bounds expected
flaw addresses. Remark 3.1 supplies the corresponding Shearer ratios.

The [Erdős #7 dossier](../../Problems/erdos-7-odd-covering-systems.md)
checks these hypotheses for canonical partial assignments using the actual
conflict graph. Its independent rare-query derivation gives the terminal
bound `nu(E) <= Omega(E) Z_(V minus N(E))/Z_V` for one fixed original output
law. That ratio is a proved specialization, not the literal statement of
Theorem 3.2(2). The source does not establish Shearer positivity for arbitrary
distinct odd congruence families or the dossier's quantitative head target.

Citation and source-boundary note only; no source text or code is vendored.
