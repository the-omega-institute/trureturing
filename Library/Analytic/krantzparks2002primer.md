---
bibkey: krantzparks2002primer
authors: Steven G. Krantz and Harold R. Parks
year: 2002
title: A Primer of Real Analytic Functions
doi: 10.1007/978-0-8176-8134-0
claim: The one-variable identity principle for real-analytic functions implies that a nonzero real-analytic function on an interval has isolated zeros.
strata_touched:
  - D5/S3/Analytic/Isolation/RationalSpanIsolation
license: citation-only
triage: anchor
---

# A Primer of Real Analytic Functions

Krantz and Parks treat the elementary identity properties of real-analytic
functions. In one real variable, the identity principle says that zeros with
an accumulation point force an analytic function to vanish identically on the
connected interval. Equivalently, a real-analytic function that is not
identically zero has isolated zeros.

The repository theorem applies this classical principle to the analytic
function obtained by subtracting one fixed rational linear combination from
the original family. Its conclusion uses Mathlib's `codiscreteWithin` filter:
the complement of the fixed level set is codiscrete within the connected
parameter set. The literature attribution is only for the identity and
isolated-zero principle. The finite rational-span packaging and its exact Lean
interface are repository specializations.

The book's first chapter is titled "Elementary Properties" and spans pages
1-23. The available publisher metadata did not expose a theorem number, so no
specific numbering or page within that chapter is claimed here.

## Search log

- 2026-08-11: Queried Crossref by title and by DOI. The records verified the
  2002 second edition, authors Steven G. Krantz and Harold R. Parks, publisher
  Birkhauser Boston, and DOI `10.1007/978-0-8176-8134-0`.
- 2026-08-11: Inspected the Springer book page and its chapter records. The
  first chapter is "Elementary Properties", pages 1-23, with DOI
  `10.1007/978-0-8176-8134-0_1`. The full text was not available in a form the
  current toolchain could inspect, so the attribution is deliberately limited
  to the standard principle and does not assert an internal theorem number.
- 2026-08-11: Searched the repository for existing identity-theorem anchors.
  `D5/L/Zeros/jaiswar2021identity` covers the complex identity theorem and
  explicitly distinguishes the Krantz-Parks real-analytic treatment, so a
  separate real-analytic note was retained rather than overloading that source.

## Verified locator

- Book: https://doi.org/10.1007/978-0-8176-8134-0
- Chapter metadata: https://doi.org/10.1007/978-0-8176-8134-0_1
