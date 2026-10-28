---
bibkey: huttonmehtavukovic2025cqoverlap
authors: Kiera Hutton; Arthur Mehta; Andrej Vukovic
year: 2025
title: "Deciding whether a C–Q channel preserves a bit is QCMA-complete"
doi: 10.48550/arXiv.2508.10664
url: https://arxiv.org/abs/2508.10664v1
claim: "Conjecture 1.5 asks whether the average overlap of outputs from k orthogonal pure inputs is at least the minimum average overlap over k distinct computational basis inputs."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap
license: citation-only
triage: anchor
---

# Hutton–Mehta–Vukovic: the orthogonal output-overlap minimum

## Verified locator

DOI: 10.48550/arXiv.2508.10664

Source: https://arxiv.org/abs/2508.10664v1

The cited version is arXiv:2508.10664v1, 14 August 2025. Definition 1.3 is on page 2; Conjecture 1.5 and the pure-state and mixed-state notation are on page 3.

## Source statements

Definition 1.3, page 2: “A C–Q channel Φ from an n-qubit space to an m-qubit space is specified by 2ⁿ states σ₁, …, σ_{2ⁿ} on m qubits and acts as Φ(ρ) = Σᵢ Tr(|i⟩⟨i| ρ) σᵢ.”

Conjecture 1.5, page 3: “Let σ₁, …, σₙ ∈ M_d(ℂ) be arbitrary quantum states. Then for any collection of k ≤ n of pairwise orthogonal pure states |u₁⟩, …, |u_k⟩ ∈ ℂⁿ, the following bound holds: (1/(k(k−1))) Σ_{r≠s} Tr((Σᵢ |⟨i|u_r⟩|² σᵢ)(Σⱼ |⟨j|u_s⟩|² σⱼ)) ≥ min_{i₁,…,i_k ∈ [n] distinct} (1/(k(k−1))) Σ_{r≠s} Tr(σ_{i_r} σ_{i_s}).”

## Mathematical reading

A pure state is a unit vector; mixed states are positive semidefinite matrices of trace one. The coordinate presentation uses `Fin n` instead of the source's one-based `[n]`. The sum counts ordered unequal pairs. Its denominator requires `2 ≤ k`. The real parts of the traces are compared in Lean; for products of states these traces are real. Injective maps from `Fin k` to `Fin n` encode the distinct basis inputs, and their finite nonempty set makes the infimum a minimum when `k ≤ n`.

The repository's settling result proves this lower bound by the squared-minor probability law and a nonnegative Hilbert–Schmidt residual. The publication supplies the question and its definitions, rather than a proof of Conjecture 1.5. The non-orthogonal correction from Theorem 3.3 is outside this statement. Equality and complexity consequences are not separate formalized conclusions here.

## Numerical corroboration

The independent experiment is `the-omega-institute/trureturing-experiments`, commit `d69f36f183a55265c3a9788695d47fad0ae307b7`, file `docs/reports/hutton-mehta-vukovic-2025-cq-output-overlap-minimum/check.py`, SHA-256 `b3e116f56441b90137e7c356e5f8bc4267af1f9988be7f995770a5af7cf4eaa0`, exit 0 as reported on issue [#20116](https://github.com/the-omega-institute/trureturing/issues/20116). This is numerical corroboration, not a proof premise.

## Literature boundary

The literature screen on #20116 identifies Lyons, *Determinantal probability measures*, Publ. Math. IHÉS 98 (2003), equation (2.1) and Theorem 5.1, as classical sources for the subset law and its inclusion probabilities. The screened later works are 2510.04943v4, 2601.17497v2 and 2601.22471v3. Completeness of the screen is `ASSUMED-UNVERIFIED`.
