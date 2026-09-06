---
bibkey: miska2016derangements
authors: Piotr Miska
year: 2016
title: Arithmetic properties of the sequence of derangements
doi: 10.1016/j.jnt.2015.11.014
claim: "For ordinary derangement numbers D_n, D_n is odd exactly when n is even; for n >= 2, v_2(D_n) = v_2(n - 1). This note attests only the parity and valuation identity."
strata_touched:
  - D5/S3/Arith/DerangementTwoAdicValuation
license: citation-only
triage: anchor
---

# Arithmetic properties of the sequence of derangements

Published in Journal of Number Theory 163 (2016), 114-145. The preprint is
arXiv:1508.01987. Section 6.1, proof of Proposition 25, printed page 48,
states: "We know that v_2(D_n) = v_2(n - 1) for any nonnegative integer n."
Here D_n denotes ordinary derangement numbers, not the separate sequences
of even and odd permutations treated in Section 5.

The Lean statement uses n >= 2 for the valuation identity, since natural
subtraction and Mathlib's total valuation at zero differ from the usual
extended valuation conventions at the initial indices. The parity law
includes the initial values D_0 = 1 and D_1 = 0. This note attests exactly
the parity and valuation statement of numDerangements_two_adic_valuation.

The exponent-divisibility corollary and the arbitrary-base perfect-power
exclusion at indices 3 modulo 4 are repository-derived. Neither is claimed
as a theorem of this source. Proposition 31 concerns finiteness of solutions
to D_n = p^k for a fixed prime p, which is a different statement.

## Verified locator

- DOI: https://doi.org/10.1016/j.jnt.2015.11.014
- Preprint: https://arxiv.org/abs/1508.01987
- PDF: https://arxiv.org/pdf/1508.01987
- Metadata: https://api.crossref.org/works/10.1016%2Fj.jnt.2015.11.014

On 2026-09-06, Crossref confirmed the author, title, journal, year, volume,
pages, and DOI above. The downloaded preprint was checked at Section 6.1,
Proposition 25, and Section 6.2, Proposition 31. The alternate title
"A note on p-adic valuations of the sequence of derangement numbers" in the
implementation brief is not the title returned for this DOI.
