---
bibkey: zeng2024sampling
authors: Zhexuan Zeng; Zuogong Yue; Alexandre Mauroy; Jorge Goncalves; Ye Yuan
year: 2024
title: A Sampling Theorem for Exact Identification of Continuous-Time Nonlinear Dynamical Systems
doi: 10.1109/TAC.2024.3409639
url: https://arxiv.org/abs/2204.14021
claim: Continuous-system identification can have generator aliases under fixed-period observations; spectral and observation-space conditions enter sampling limits.
strata_touched:
  - D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Spectral phase ambiguity is a dynamical identification question

IEEE Transactions on Automatic Control 69(12), 8402-8417. The journal metadata and the arXiv PDF's parsed discussion of generator aliasing, exponential/logarithm ambiguity and observation-space assumptions were read. The page introducing the infinite-dimensional aliasing discussion was rendered. The article's general nonlinear recovery claims are not used as premises for the new finite-dimensional bounds.

The arithmetic-clock draft independently proves a Hilbert-Schmidt estimate for Hermitian A,B and a map X: two finite-time intertwining defects at delays tau and phi*tau bound AX-XB, given a finite cross-spectral bandwidth. An algebraic norm in Q(sqrt(5)) supplies an explicit O(bandwidth^2) constant. The repository's exact Fibonacci residual supplies matching near-alias examples. Finite rational clock ratios are admitted through a separate calibration margin.

These are paper-level sufficient estimates, not a proof that the golden ratio optimizes every finite experimental budget. Frobenius norm is not silently replaced by operator or diamond norm. The channel specialization still requires CPTP and Gibbs calibration to be checked independently, and acquiring full superoperator residuals is an experimental resource rather than a free scalar observation. Non-normal dynamics and unbounded generators are outside the stated theorem.

The study does not infer P=NP, WSS progress, a universal physical frequency, or an already verified Lean extension. The intended Section 18 remains an append draft in PR #8891 discussion until the main-volume file is updated.
