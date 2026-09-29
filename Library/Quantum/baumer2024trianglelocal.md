---
bibkey: baumer2024trianglelocal
authors: Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner
year: 2024
title: "Exploring the local landscape in the triangle network"
doi: 10.48550/arXiv.2405.08939
url: https://arxiv.org/abs/2405.08939v1
claim: "Local models in the triangle network reach a fully symmetric four-outcome distribution with p(A=B=C) = 1/4; the paper conjectures that local fully symmetric distributions have maximal p(A=B=C) very close to 1/4, and asks as an open problem whether a local fully symmetric distribution with p(A=B=C) > 1/4 exists."
strata_touched:
  - D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation
license: citation-only
triage: anchor
---

# Exploring the local landscape in the triangle network

E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner, arXiv:2405.08939
(v1 2024-05-14, the only version); Phys. Rev. A 111, 052453 (2025).
Subject: quant-ph.

In the triangle network three independent sources α, β, γ each feed two of the
parties Alice, Bob and Charlie. A distribution `p(a, b, c)` is local if

> p(a,b,c) = ∫_{[0,1]^{×3}} dα dβ dγ p_A(a|β,γ) p_B(b|γ,α) p_C(c|α,β),

with α, β, γ uniform on `[0, 1]` and conditional distributions `p_A`, `p_B`,
`p_C` (eq. `trilocal`). A distribution with four outcomes per party is fully
symmetric if it is invariant under permutations of the parties and under joint
permutations of the outcomes; `s₁₁₁ = p(A = B = C)`. The paper constructs local
fully symmetric models with `s₁₁₁ = 1/4`, estimates local bounds with neural
networks, and states in its conclusion:

> Open problem. Does there exist a distribution p(A,B,C) that is local in the
> triangle network and fully symmetric such that p(A=B=C) > 1/4?

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2405.08939
- URL: https://arxiv.org/abs/2405.08939v1 (source of v1 retrieved 2026-09-29).
- Location: §2 ("Setup: locality and symmetry") for eq. `trilocal` and the
  definition of fully symmetric distributions; the section on inequalities for
  `eq:ineq_l1` and `eq:ineq_l2`; the Conclusion for the open problem.
