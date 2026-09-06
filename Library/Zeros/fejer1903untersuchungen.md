---
bibkey: fejer1903untersuchungen
authors: Leopold Fejer
year: 1903
title: Untersuchungen uber Fouriersche Reihen
doi: 10.1007/BF01447779
claim: The Fejer kernel has triangular signed Fourier coefficients and is a normalized squared geometric exponential sum, hence is nonnegative.
strata_touched:
  - D5/S3/Zeros/Repulsion/FejerNearCollisionBound
license: citation-only
triage: anchor
---

# Untersuchungen uber Fouriersche Reihen

This note attributes the classical Fejer kernel and its normalized-square
identity to the literature. The normalization used in the Lean module is
the sum over integer modes with absolute value strictly below M, with weight
one minus the absolute mode divided by M. Pairing conjugate modes gives the
real cosine sum; the normalized square makes its nonnegativity explicit.

The attribution covers the kernel definition and square identity. It does
not claim that this article states the repository's ordered near-pair or
multiplicity bounds verbatim. Those finite-family specializations are derived
in the repository, and imply no asymptotic assertion about simple zeta zeros.

## Search Log

- 2026-09-06: Crossref bibliographic search for
  `Fejer Untersuchungen Fouriersche Reihen 1904` identified this article.
  The exact DOI record confirms the author, title, Mathematische Annalen 58,
  pages 51-69, and publication date March 1903. The year here follows that
  record rather than the initial search's tentative year.
- 2026-09-06: The Fejer-kernel reference page below displays the signed
  triangular Fourier expansion, normalized sine-square formula and
  nonnegativity. No internal theorem number in the original article is
  asserted; its full text has not been inspected in this attempt.
- Repository Library search found no existing Fejer or Fourier-kernel note.

## Verified locator

- DOI metadata: https://api.crossref.org/works/10.1007/BF01447779
- Article: https://doi.org/10.1007/BF01447779
- Formula reference: https://en.wikipedia.org/wiki/Fej%C3%A9r_kernel
