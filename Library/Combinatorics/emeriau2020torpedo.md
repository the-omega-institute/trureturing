---
bibkey: emeriau2020torpedo
authors: Pierre-Emmanuel Emeriau; Mark Howard; Shane Mansfield
year: 2022
title: "Quantum Advantage in Information Retrieval"
doi: 10.1103/PRXQuantum.3.020307
url: https://arxiv.org/abs/2007.15643v2
claim: "In the dimension-d Torpedo Game, Alice receives x, z in Z_d, sends one dit, and Bob, asked q in {infinity, 0, ..., d-1}, must answer a != x (q = infinity) or a != qx - z; the classical value is theta^C_2 = 3/4, theta^C_3 = 11/12, perfect classical strategies were found for 5 <= d <= 23, and the authors conjecture theta^C_(d>=5) = 1 (eq. (11))."
strata_touched:
  - D5/S3/Quantum/Information/TorpedoGamePerfectClassical
license: citation-only
triage: anchor
---

# Quantum Advantage in Information Retrieval

P.-E. Emeriau, M. Howard and S. Mansfield, arXiv:2007.15643 (v1 2020-07-30,
v2 2020-11-19); PRX Quantum 3, 020307 (2022). Subject: quant-ph.

The paper studies information retrieval tasks in prepare-and-measure
scenarios. In the dimension-`d` Torpedo Game Alice receives two dits `x, z`,
sends a single (qu)dit, and Bob is asked one of `d + 1` questions
`q ∈ {∞, 0, …, d − 1}`; the winning relations are
`w_∞(x, z) = {a ≠ x}` and `w_q(x, z) = {a ≠ qx − z}`, arithmetic modulo `d`
(eq. (2)). The classical value `θ^C_d` is the greatest average winning
probability over encodings and decodings with shared randomness (eq. (cval)).
The authors find `θ^C_2 = 3/4`, `θ^C_3 = 11/12`, and write:

> We have, however, found perfect classical strategies, i.e. strategies that
> win with probability 1, for d = 5 (see Fig. 9) up to d = 23. This leads us to
> conjecture that there exists a perfect classical strategy for all d > 5,
> Conjecture: θ^C_{d≥5} = 1.

The thesis of P.-E. Emeriau (arXiv:2204.08782, 2022) restates the conjecture
for dimension 4 and above.

## Verified locator

- DOI: https://doi.org/10.1103/PRXQuantum.3.020307 (open access): the section
  on the Torpedo Game, eq. (11), Fig. 9.
- URL: https://arxiv.org/abs/2007.15643v2 (source retrieved 2026-09-30):
  `S1_QRAC.tex` (winning relations), `S3_Torpedo.tex` (eq. `cval`, the
  conjecture `PerfectClassical`), `cl_dimension5.tex` (Fig. 9).
