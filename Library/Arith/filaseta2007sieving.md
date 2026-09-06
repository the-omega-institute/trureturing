---
bibkey: filaseta2007sieving
authors: Michael Filaseta, Kevin Ford, Sergei Konyagin, Carl Pomerance, Gang Yu
year: 2007
title: Sieving by large integers and covering systems of congruences
doi: 10.1090/S0894-0347-06-00549-2
claim: "The introduction explicitly states that the reciprocal sum of the moduli of a covering system is at least 1. For distinct moduli greater than 1 it records the strict inequality, with a proof attributed to M. Newman, and deduces that a covering integer H satisfies sigma(H)/H > 2. The covering-system setting is attributed to Erdos (1950). This note attests these necessary conditions, not an explicitly stated two-odd-prime L/8 density theorem."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Necessary Conditions for Covering Systems

The introduction states: "It is easy to see that in a covering system, the
reciprocal sum of the moduli is at least 1." It later gives Newman's argument
for strict inequality when the moduli are distinct and greater than 1, and
states that if H is covering, then sigma(H)/H > 2.

These are the literature statements used for provenance. The Lean module
specializes the density argument to distinct odd primes p and q and arbitrary
natural exponents A and B. Its two inductive geometric estimates establish
8 sigma(p^A q^B) <= 15 p^A q^B, yielding at least one eighth uncovered.
That quantitative statement was not found explicitly in this source.

## Verified locator

- DOI: https://doi.org/10.1090/S0894-0347-06-00549-2
- Exact scope: introduction, journal pages 495-496, the reciprocal-sum
  conditions and the paragraph beginning "Say an integer H".
- Journal metadata: Journal of the American Mathematical Society 20 (2007),
  495-517; Crossref DOI record verified on 2026-09-06.
- Read text: https://arxiv.org/html/math/0507374v3, Section 1, before
  Conjecture 1 and in the paragraphs introducing a covering integer H.
- Author-hosted version: https://math.dartmouth.edu/~carlp/PDF/covfinal.pdf.
- Hough-Nielsen, arXiv:1703.02133v2, and the uncovered-density paper,
  arXiv:1811.03547v1, were also searched. Neither supplied an explicit
  two-odd-prime L/8 statement. The latter cites this survey as reference [7].

The source's historical conjectures and status claims are not adopted as
current claims. This formalization does not resolve the general odd covering
problem or assert a new exclusion beyond the classical necessary condition.
