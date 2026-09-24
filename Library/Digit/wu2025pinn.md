---
bibkey: wu2025pinn
authors: Huiling Wu; Sen-Yue Lou
year: 2025
title: "Permutation-Invariant Niven Numbers"
doi: 10.3390/sym18010186
url: https://arxiv.org/abs/2508.01611
claim: "Section 8.4 conjectures that, after excluding the stated cases, no permutation-invariant Niven numbers have digit sums outside 3 through 81."
strata_touched:
  - D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum
license: citation-only
triage: anchor
---

# Permutation-Invariant Niven Numbers

Huiling Wu and Sen-Yue Lou study decimal permutation-invariant Niven numbers.
This note records only the section 8.4 digit-sum bound used by the formal result.

## Verified locator

- arXiv: https://arxiv.org/abs/2508.01611 (version 3, 2025-10-26)
- DOI: https://doi.org/10.3390/sym18010186
- Section: 8.4, PDF page 12

The source states that, for the nontrivial distinct-digit cases under discussion,
the digit sum satisfies `3 <= Sigma(PINN) <= 81`, and conjectures that no exceptions
exist beyond the excluded cases. The formal result settles the upper-bound clause
for the source-faithful `DecimalPINN` model. Its `3 | Sigma(PINN)` component is
literature-attested through the cited Theorem 1 consequence; the `Sigma(PINN) <= 81`
component is repository-derived.

The journal landing page was confirmed through Crossref, but the journal text was
not readable in this run because the MDPI page returned HTTP 403. That journal-text
boundary is `ASSUMED-UNVERIFIED`; the arXiv version and locator above are the
available source basis.
