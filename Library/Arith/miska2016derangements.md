---
bibkey: miska2016derangements
authors: Piotr Miska
year: 2016
title: Arithmetic properties of the sequence of derangements
doi: 10.1016/j.jnt.2015.11.014
claim: The parity law for derangement numbers and the identity v_2(D_n) = v_2(n - 1).
strata_touched:
  - D5/S3/Arith/DerangementTwoAdicValuation
license: citation-only
triage: anchor
---

# Arithmetic Properties of the Sequence of Derangements

Piotr Miska studies arithmetic properties of the ordinary derangement numbers
`D_n` in the *Journal of Number Theory* 163 (2016), pp. 114-145. The article
records their parity behavior and, in Section 6.1 (printed p. 48, in the proof
of Proposition 25), states: "We know that v_2(D_n) = v_2(n - 1) for any
nonnegative integer n." This note attributes those two statement-level facts
to the literature.

The repository proof does not import the article's proof route. It reconstructs
the parity invariant by two-step induction on Mathlib's derangement recurrence
and derives the exact valuation by cancelling the resulting odd factor. The
bundled conclusion that a power exponent divides the valuation, and the
companion exclusion at indices congruent to three modulo four, are
repository-derived corollaries rather than claims attributed to Miska.

## Search log

- 2026-09-05: The prior implementation attempt located the quoted valuation
  identity in arXiv:1508.01987, Section 6.1, printed p. 48, while checking the
  provenance requirement registered in PZG_BEDC.md remark 27.826.
- 2026-09-05: Queried Crossref by exact title and author. The first result
  matched Piotr Miska, the title, journal, volume 163, year 2016, and pages
  114-145, and returned DOI `10.1016/j.jnt.2015.11.014`.

## Verified locator

- DOI: https://doi.org/10.1016/j.jnt.2015.11.014
- arXiv: https://arxiv.org/abs/1508.01987
