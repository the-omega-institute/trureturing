---
bibkey: ribeszalesskii2010profinite
authors: Luis Ribes; Pavel Zalesskii
year: 2010
title: Profinite Groups
doi: 10.1007/978-3-642-01642-4
claim: Profinite completion is modeled by compatible finite quotient readings, and the canonical image of the original group is dense in that completion.
strata_touched:
  - D5/S1/Dynamics/ProfiniteIntegers
license: citation-only
triage: anchor
---

# Profinite Groups

Ribes and Zalesskii's monograph is a standard reference for profinite groups
and their completions. This note anchors only the classical background used
by `D5/S1/Dynamics/ProfiniteIntegers`: a profinite completion is assembled
from compatible finite quotients, and the canonical group image is dense.

The repository theorem is more specific. It models the profinite integers by
compatible readings in `ZMod m` and proves that the image of the natural
numbers, not only the additive integers, is both injective and dense. Its
finite-window proof chooses one representative at a common product modulus.
That strengthening and its Lean proof are repository-derived; this note does
not attribute them to a numbered result in the monograph.

## Search log

- 2026-08-11: Searched the pinned Mathlib checkout for profinite completion,
  `DenseRange`, natural-number casts, and compatible residue families.
  `ProfiniteGrp.ProfiniteCompletion.denseRange` proves density of the
  canonical image for an arbitrary group. No natural-number-density theorem
  for the profinite completion of the integers was found.
- 2026-08-11: Queried Crossref by DOI. The returned metadata verified DOI
  `10.1007/978-3-642-01642-4`, title *Profinite Groups*, authors Luis Ribes and
  Pavel Zalesskii, publisher Springer Berlin Heidelberg, and publication year
  2010. The full text was not inspected, so no theorem number or page-level
  locator is claimed.

## Verified locator

- DOI: https://doi.org/10.1007/978-3-642-01642-4
