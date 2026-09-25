---
bibkey: scarlett2021fano
authors: Jonathan Scarlett; Volkan Cevher
year: 2021
title: An Introductory Guide to Fano's Inequality with Applications in Statistical Estimation
doi: 10.1017/9781108616799.017
url: https://arxiv.org/abs/1901.00555v3
claim: Fano reductions and conditional mutual-information bounds provide algorithm-independent lower bounds, including adaptive measurement settings.
strata_touched:
  - D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn
license: citation-only
triage: anchor
---

# An information budget for fixed-amplitude phase readings

The chapter appears in Information-Theoretic Methods in Data Science, Cambridge University Press (2021); the arXiv v3 version is dated 2019-11-25. Parsed Sections 2.1 and 3.2 and Appendix A.6 were read. The page starting Section 2 was rendered and checked. The appendix explicitly tracks how adaptive input selection enters the mutual-information chain rule.

The Section 19 draft selects a finite packing of frequencies and observes a unit-modulus signal plus independent two-dimensional Gaussian noise. Conditional on earlier measurements, each new signal covariance has trace at most one. Gaussian maximum entropy gives a fixed per-reading mutual-information bound; Fano then lower-bounds the number of readings, including adaptive time choices. This is a new application in the same model, not a new Fano inequality.

The statement uses fixed signal amplitude, known noise variance and a fixed total number of observations. Different probe energy, quantum access, stopping-time budgets or unknown calibration need their own arguments. The constructive dyadic decoder currently retains a log-log gap relative to this information lower bound, so minimax optimality is not claimed. No Lean kernel or independent proof audit is implied by the Scribe reference.
