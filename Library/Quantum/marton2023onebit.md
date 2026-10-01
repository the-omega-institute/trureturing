---
bibkey: marton2023onebit
authors: István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi
year: 2023
title: "Beating one bit of communication with and without quantum pseudo-telepathy"
doi: 10.48550/arXiv.2308.10771
url: https://arxiv.org/abs/2308.10771v1
claim: "Two parallel copies of the CGLMP_d game have one-bit classical bound 12 for d = 2, ..., 10, and the authors conjecture this for every d >= 2; the truncations [CGLMP_d^{⊗2}]_s and [CGLMP_d^{⊗2}]_a have conjectured local bounds 7 and 4, verified up to d = 20."
strata_touched:
  - D5/S3/Quantum/Information/DoubleCglmpOneBitBound
license: citation-only
triage: anchor
---

# Beating one bit of communication with and without quantum pseudo-telepathy

I. Márton, E. Bene, P. Diviánszky and T. Vértesi, arXiv:2308.10771 (v1
2023-08-21, the only version); npj Quantum Information 10, 79 (2024).
Subject: quant-ph.

The paper looks for Bell-type inequalities that local hidden variables cannot
satisfy even when one bit of classical communication is allowed. A local
behaviour is `P(ab|xy) = ∫ q(λ) P_A(a|xλ) P_B(b|yλ)` (eq. P_LHV); with one bit
`l = l(x, λ)` from Alice to Bob, Bob's response is `P_B(b|y l λ)`
(eq. P_LHV1bit), and the largest value of a Bell expression over these models is
the one-bit bound `L1bit`. With outputs `0, …, d − 1`,

> CGLMP_d = P(A₀ ≥ B₀) + P(A₀ ≤ B₁) + P(A₁ < B₀) + P(A₁ ≥ B₁) ≤ 3,

and two copies are played in parallel. The authors state:

> The one-bit bound L1bit(CGLMP_d^{⊗2}) = 12 in the last column is verified by
> the branch-and-bound algorithm up to d = 10. We conjecture that this is the
> exact bound for any d ≥ 2.

For the truncations to the inputs `{00, 01, 11}` of both parties, and to
`{00, 01, 11}` and `{00, 11}`, they give "the conjectured local bound" 7
("which we verified up to d = 20") and "the conjectured local bound L = 4,
which we verified up to d = 20".

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2308.10771
- URL: https://arxiv.org/abs/2308.10771v1 (source of v1 retrieved 2026-09-29).
- Location: the section on notation for eqs. (P_LHV) and (P_LHV1bit); the
  section on CGLMP_d inequalities for eq. (cglmpineq), Table IV and the
  conjecture; the subsections on the truncated double CGLMP inequalities for
  the bounds 7 and 4.
