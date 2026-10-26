---
bibkey: wong2026leeyang
authors: Benjamin Wong; Sergey Bravyi; David Gosset; Yinchen Liu
year: 2026
title: Lee-Yang tensors and Hamiltonian complexity
doi: 10.48550/arXiv.2602.03605
url: https://arxiv.org/abs/2602.03605v1
claim: "Section 5.6 asks whether Conjectures 1,2,3 extend to phase-shifted EPR-like Hamiltonians; the four-cycle with pi flux refutes the extension of Conjecture 2."
strata_touched:
  - D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation
license: citation-only
triage: anchor
---

# Lee-Yang tensors and Hamiltonian complexity

## Verified locator

DOI: 10.48550/arXiv.2602.03605

Source: https://arxiv.org/abs/2602.03605v1

Conjecture 2, Section 5.5, p. 24:

> Suppose n ≥ 2, s ∈ [0, 1), and the interaction graph is connected. Then the second smallest eigenvalue of H_s coincides with the smallest eigenvalue of H_s restricted to the odd-weight subspace.

Section 5.6, p. 26:

> Define a two-qubit operator h(z) = |00⟩⟨00| + z|11⟩⟨00| + z*|00⟩⟨11| + |z|²|11⟩⟨11|, where z ∈ ℂ.

> A phase-shifted EPR-like Hamiltonian is defined as H_s(θ) = −Σ_{(p,q)∈E} h_{p,q}(se^{iθ_{p,q}}), (77) where s ∈ [0,1] and θ_{p,q} ∈ [0,2π) are arbitrary edge-dependent angles (phase shifts). Setting θ_{p,q} = 0 gives the original EPR-like Hamiltonian H_s.

> We leave as an open question whether Conjectures 1,2,3 hold for phase-shifted EPR-like Hamiltonians.

The formal refutation uses four sites, s = 3/5, edges {0,1}, {0,3}, {1,2}, {2,3}, and phase π only on {0,3}. Two distinct full-space eigenvalues are below −5/2, while the odd-sector spectrum is above −5/2. The conclusion does not settle Conjecture 2 without phase shifts, the simplicity of the second eigenvalue, a whole interval of parameters, or the phase-shifted Conjecture 3.

The supporting experiment is `docs/reports/wong-bravyi-gosset-liu-2026-phase-shifted-conjecture-2/check.py` in `the-omega-institute/trureturing-experiments`, commit `f55c81f21d6288891d11b00f8b56992a1cdcc597`, SHA-256 `1f0420b714cff8a5de260b1ef7230c6f2eed1dec54aac146895fd8902c4dcf88`; `python3 check.py` exits 0 with `RESULT PASS` in the preregistration reading. The formal conclusion uses the Lean kernel certificate. Literature completeness beyond the source and the screen in issue #18759 is ASSUMED-UNVERIFIED.
