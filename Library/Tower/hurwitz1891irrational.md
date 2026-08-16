---
bibkey: hurwitz1891irrational
authors: Adolf Hurwitz
year: 1891
title: Ueber die angenaeherte Darstellung der Irrationalzahlen durch rationale Brueche
doi: 10.1007/BF01206656
claim: Every irrational has infinitely many rational approximants at the sharp reciprocal-square-root-five scale, with the golden continued-fraction class extremal.
strata_touched:
  - D5/S0/Tower/Hardness/RationalSpectrum
license: citation-only
triage: anchor
---

# Ueber die angenaeherte Darstellung der Irrationalzahlen durch rationale Brueche

Hurwitz's paper is the classical source for the sharp Diophantine-approximation
constant `1 / sqrt(5)`.  In normalized regular-continued-fraction coordinates,
every irrational orbit has lower-limit approximation coefficient at most this
constant, and the continued-fraction class with an all-one tail attains it.

The repository declaration expresses the same extremum as a least element of
the set of upper bounds of the hardness spectrum.  This is the order-correct
reading of the source atom's phrase "the bottom of the supremum structure": the
hardness values themselves have sharp supremum `1 / sqrt(5)`.

## Search log

- 2026-08-17: Searched D5 declarations first.  The exact local declarations
  `D5.S1.Depth.golden_hurwitz_bound` and
  `D5.S3.AnalyticClosure.GoldenApproximationConstant.golden_fibonacci_approximation_constant_tendsto`
  cover a golden-ratio lower bound and the Fibonacci attainment limit,
  respectively.  Neither supplies the universal sharp upper bound, and their
  S1/S3 modules cannot be imported upward into the required S0 destination.
- 2026-08-17: Queried Crossref directly by DOI.  The resolver returned Adolf
  Hurwitz, the article title, June 1891, *Mathematische Annalen* volume 39,
  pages 279-284, and DOI `10.1007/BF01206656`.
- 2026-08-17: Queried the public summary of Hurwitz's number-theory theorem to
  confirm the irrational rational-approximation attribution.  The Springer PDF
  endpoint returned an access-check HTML page, so no claim of inspecting the
  article PDF is made.
- 2026-08-17: Searched pinned Mathlib v4.31.0, Loogle, LeanSearch, and GitHub
  Lean code for the sharp theorem and badly-approximable formulation.  Only
  Dirichlet's constant-one theorem, Legendre's constant-one-half criterion,
  golden-ratio identities, and Liouville-style results were found.  No exact
  reusable sharp Hurwitz theorem was found, so the repository declaration uses
  a direct normalized continued-fraction proof.

## Verified locator

- DOI: https://doi.org/10.1007/BF01206656
