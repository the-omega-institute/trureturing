---
bibkey: zhanguptahillery2024detectorsensor
authors: C. Zhan, H. Gupta, M. Hillery
year: 2024
title: Optimizing Initial State of Detector Sensors in Quantum Sensor Networks
doi: 10.1145/3655028
url: https://arxiv.org/abs/2306.17401v6
claim: Section 5, Conjecture 1 proposes a uniform coefficient-square state on any weight partition minimizing the common final-state overlap as an optimal initial detector-sensor state.
strata_touched:
  - D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1145/3655028

Source: https://arxiv.org/abs/2306.17401v6

ACM Transactions on Quantum Computing 5(2), Article 10 (2024).

## Statement

Section 5, Conjecture 1, page 10:

> Consider the ISO problem, with the unitary operator 𝑈, initial state |𝜓⟩, and final states {|𝜙ᵢ⟩} as defined therein. Recall that the eigenvalues of 𝑈 are {𝑒^{+𝑖𝜃}, 𝑒^{−𝑖𝜃}}. Let 𝑛 ≥ 3 be the number of sensors. For a given 𝜃 ∈ (0,𝑇] ∪ [180 − 𝑇, 180), degrees, where 𝑇 is from Theorem 2, the optimal initial state |𝜓⟩ for the ISO problem is as follows. Let 𝑆ₗ be the partition that minimizes (𝑅ₗ + cos(2𝜃)𝐿ₗ)/(𝑅ₗ + 𝐿ₗ), where 𝑅ₗ and 𝐿ₗ are as defined in the previous section. The coefficients of the optimal solution are such that their coefficient-squares are given by: |𝜓ⱼ|² = 1/|𝑆ₗ| ∀ |𝜓ⱼ|² ∈ 𝑆ₗ  |𝜓ⱼ|² = 0 ∀ |𝜓ⱼ|² ∉ 𝑆ₗ

## Encoding and boundary

The tensor eigenbasis is `Fin n → Bool`, with true denoting u₊ and false denoting u₋. The number of true entries gives the weight. Angles are measured in radians. The threshold is `Real.arccos (-((q - 1) / q)) / 2`, where `q = (n + 1) / 2` uses natural-number division. The real-equation counts are the cardinalities of weight-k words with equal and unequal selected bits. A weight-l class contains `Nat.choose n l` words.

The repository conclusion compares every normalized competitor and every global equal-prior POVM with an attaining POVM for every proposed state, allowing arbitrary coefficient phases. Permutation averaging of Gram decompositions, a positive semidefinite trace certificate, monotonicity of the square-root diagonal, and square-root-measurement attainment supply the proof. The source’s stronger strict-averaging Conjecture 2 is not required.

The full-angle combination, ancillary and mixed probes, unequal priors, multiple simultaneous firing events, and noisy channels are outside this conclusion.
