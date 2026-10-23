---
bibkey: sarkis2026starbattery
authors: Matthieu Sarkis, Oskar A. Prośniak, Samuel Nigro, Alexandre Tkatchenko
year: 2026
title: "Star Topology Optimizes the Charging Power of Quantum Batteries"
doi: 10.48550/arXiv.2603.10853
url: https://arxiv.org/abs/2603.10853v1
claim: "For a quantum battery of N fermionic cells coupled by a graph G, the early-time charging power at zero local field is maximized by the star graph (Theorem 1). With a local field, the power is a weighted mean of the uniform overlaps w_k = (1ᵀu_k)² of the adjacency eigenvectors; Conjecture 1 asserts that the overlap of the lowest adjacency eigenspace satisfies w_min(G) ≤ N/2 − √(N − 1), the star's value, for every non-empty graph on N vertices."
strata_touched:
  - D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation
license: citation-only
triage: anchor
---

# Sarkis–Prośniak–Nigro–Tkatchenko, star topology and quantum-battery charging power

M. Sarkis, O. A. Prośniak, S. Nigro and A. Tkatchenko, *Star Topology Optimizes the Charging Power of Quantum Batteries*, arXiv:2603.10853 [quant-ph] (v1 11 March 2026), DOI 10.48550/arXiv.2603.10853.

## Verified locator

DOI: 10.48550/arXiv.2603.10853 (the arXiv DOI; no journal version is listed on the abstract page).
Primary version read: https://arxiv.org/abs/2603.10853v1 (the only arXiv version).
Source: https://arxiv.org/pdf/2603.10853v1 (text read from the PDF):
- §III.A, Eqs. (11) and (14), the uniform overlaps and the mode energies;
- §III.C, Observation 2, Eq. (23), and Conjecture 1, Eq. (24).

## Source statements

§III.A, Eq. (11): "Let A = O diag(ε₁, …, ε_N) Oᵀ with O ∈ O(N) and orthonormal eigenvectors u_k (columns of O), Au_k = ε_k u_k. Define the uniform overlaps and weights v_k = 1ᵀu_k, w_k = v_k² ≥ 0." Eq. (14): "Set E_k(h) := (N/M) ε_k + h".

§III.C: "Our special attention deserves the following quantity w_min := Σ_{k′} w_{k′}, where k′ are such that E_{k′}(h) = min_k E_k(h)". Observation 2 gives the star's value w_min(S) = N/2 − √(N − 1), Eq. (23).

Conjecture 1: "(Star optimality for the uniform overlap). Let G be a non-empty graph on N vertices. Its minimal energy uniform overlap w_min(G) is upper bounded by w_min(G) ≤ w_min(S) = N/2 − √(N − 1). (24)" The authors write that it rests on an "exhaustive numerical check of graphs with N ≤ 7 and sample check of larger random graphs".
