---
bibkey: medina2015fibonacciregularity
authors: L. A. Medina; E. Rowland
year: 2015
title: p-regularity of the p-adic valuation of the Fibonacci sequence
doi: null
url: https://arxiv.org/abs/0910.2907
claim: Theorem 1.4 restates Lengyel's Fibonacci valuation formulas for every prime, retaining the initial rank valuation and the separate formulas for two and five.
strata_touched: []
license: citation-only
triage: anchor
---

# Fibonacci valuations for every prime

## Verified locator

L. A. Medina and E. Rowland, *p-regularity of the p-adic valuation of the
Fibonacci sequence*, The Fibonacci Quarterly 53(3) (2015), 265–271.
The arXiv record https://arxiv.org/abs/0910.2907 gives the journal reference;
Theorem 1.4 (Lengyel) is on page 2 of arXiv:0910.2907v4 (26 January 2015),
https://arxiv.org/pdf/0910.2907v4 .
The proposed DOI 10.1080/00150517.2015.12427843 returns HTTP 404 from
Crossref and doi.org (checked 2026-09-16); the attested locator is arXiv.

## Claim and scope

Write alpha(p) for the least positive index with p dividing F_n. For n>=1,
Theorem 1.4 states v_5(F_n)=v_5(n), and

- v_2(F_n)=v_2(n)+2 when n is zero modulo six;
- v_2(F_n)=1 when n is three modulo six;
- v_2(F_n)=0 in the other four residue classes modulo six.

For a prime p outside {2,5}, v_p(F_n)=v_p(n)+v_p(F_alpha(p)) when
alpha(p) divides n, and v_p(F_n)=0 otherwise. The initial valuation
v_p(F_alpha(p)) is not assumed to be one.

These formulas imply the square-transport equivalence in FPD.1 of
`Problems/wall-sun-sun-golden-unit-lift.md` for positive multipliers;
the zero multiplier is handled separately by F_0=0. The full valuation
formula is attributed to Lengyel, rather than claimed as a new consequence
of the dossier. The paper's computational WSS bound is historical.
