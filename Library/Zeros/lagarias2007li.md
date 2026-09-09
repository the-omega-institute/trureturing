---
bibkey: lagarias2007li
authors: Jeffrey C. Lagarias
year: 2007
title: Li Coefficients for Automorphic L-Functions
doi: 10.5802/aif.2311
claim: The pole-removed completed automorphic L-function is entire of order one; the trivial representation gives twice the classical Riemann xi function.
strata_touched:
  - D5/S3/Analytic/XiGlobalGrowth
license: citation-only
triage: anchor
---

# Li Coefficients for Automorphic L-Functions

Theorem 2.1(6) states that the pole-removed function `xi(s, pi)` is entire
of order one and maximal type. Its standing hypothesis is an irreducible
cuspidal unitary automorphic representation over the rationals. The paragraph
immediately before Theorem 2.1 explicitly includes the trivial representation
of GL(1), for which `xi(s, pi_triv) = 2 xi(s)`. The simple poles at zero and
one have been removed in this normalization.

Consequently, for the classical xi function there is a positive real constant
C such that `|xi(s)| <= exp(C (1 + |s|)^(3/2))` for every complex s. This is a
weaker consequence of order one, not the literal statement of Theorem 2.1(6).
The factor two and a bounded initial disk can be absorbed into C. No Riemann
hypothesis is required for this consequence.

`D5/S3/Analytic/XiGlobalGrowth.xi_reading_norm_le_exp_three_halves` proves
this consequence directly from the existing symmetric theta-Mellin integral.
It does not formalize automorphic representations, an order-one theorem,
Hadamard factorization, or the paper's Li coefficient identities. Its private
integrand estimate keeps an unspecified positive theta decay rate and the
whole initial integration interval. The actual Lean xi is the global
pole-removed definition, including its values at zero and one.

## Verified locator

- Read on 2026-09-09: https://arxiv.org/html/math/0404394, the normalization
  preceding Theorem 2.1, all six clauses of the theorem, and its proof of (6).
  The proof treats the trivial representation's poles explicitly. Its later
  informal statements about the meromorphic completion are not used as
  formulas at the two poles.
- Crossref's exact author/title query on 2026-09-09 matched Jeffrey C. Lagarias,
  this title, and DOI https://doi.org/10.5802/aif.2311.
- Published in Annales de l'Institut Fourier 57 (2007), 1689–1740.
