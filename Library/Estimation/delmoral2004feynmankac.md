---
bibkey: delmoral2004feynmankac
authors: Pierre Del Moral
year: 2004
title: "Feynman-Kac Formulae: Genealogical and Interacting Particle Systems with Applications"
doi: 10.1007/978-1-4684-9393-1
url: https://link.springer.com/content/pdf/bfm:978-1-4684-9393-1/1
claim: "The book's preface and contents locate discrete Feynman–Kac path models, distribution flows and semigroup methods; the note uses it only as a method reference."
strata_touched: []
license: citation-only
triage: anchor
---

# Feynman–Kac path weights and the native counting law

## Verified locator

DOI: <https://doi.org/10.1007/978-1-4684-9393-1> resolves with HTTP
200 to Springer's book record. Crossref confirms Del Moral, 2004
and the electronic ISBN 9781468493931. The accessible
[publisher front matter](https://link.springer.com/content/pdf/bfm:978-1-4684-9393-1/1)
is a 16-page PDF, HTTP 200, identifying the full title and author.
Its preface and contents were inspected. They locate path models in
section 1.3, distribution flows in section 2.5 and
semigroups in section 2.7. The chapter-2 PDF endpoint supplies only
the chapter's HTML record; Firecrawl returns HTTP 402. No numbered
theorem from the unavailable chapter text is asserted here.

## Method correspondence

Weighting a Markov path by potentials and summing over intermediate
states is the discrete Feynman–Kac method. Normalized conditional
flows additionally divide by their total unnormalized mass. These
two operations must be distinguished: an algebraic weighted sum
can be meaningful even when a complex potential does not define a
positive probability law.

Section 120 of the
[spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses an actual positive Markov path law, then multiplies each edge
by its count-generating factor. Its exact prefix/last-edge sum is
a finite version of the path-weighting method. The directly checked
finite forward calculation is also described in the
[Rabiner note](rabiner1989hiddenmarkov.md).

Neither this methodological attribution nor generic particle-system
convergence supplies the parity compensation identities, the actual
count-event correspondence, the complex generating-function error,
or the relative Poisson coefficient estimate. The native arithmetic
small-ball argument additionally retains a positive conditioning
denominator and the complete moving posterior center. No particle
approximation theorem or general Feynman–Kac estimate is imported
as a replacement for those model-specific obligations.
