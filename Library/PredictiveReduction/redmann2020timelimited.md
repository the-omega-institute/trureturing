---
bibkey: redmann2020timelimited
authors: Martin Redmann
year: 2020
title: An L2_T-error bound for time-limited balanced truncation
doi: 10.1016/j.sysconle.2019.104620
url: https://arxiv.org/abs/1907.05478
claim: Time-limited balanced truncation has an existing finite-time error theory based on discarded time-limited singular values.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Time-limited error bounds

## Source and locator

Systems & Control Letters 136, 104620 (2020); the preprint was submitted in 2019. Publisher metadata and arXiv:1907.05478 were checked. The parsed PDF's Theorem 2.2 and its assumptions were read. Screenshot retrieval failed, so no page-image or chart verification is asserted.

The source supplies an input-output error estimate for time-limited balanced truncation with zero initial state and an input-energy budget. Its treatment is prior art for explicit finite-horizon approximation bounds.

## Dependency boundary

The repository's Section 14 uses random initial-state inference and subsequent autonomous rollout, not the source's zero-initial-state input experiment. Its deterministic parameter-perturbation budget is derived for that separate loss. The source is not used to infer an unknown generator's estimation accuracy, nor to claim structure preservation for every balanced truncation.

This is citation-only context. No source implementation, hardware experiment, or complete independent proof audit was performed.
