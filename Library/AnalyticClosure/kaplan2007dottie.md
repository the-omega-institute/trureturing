---
bibkey: kaplan2007dottie
authors: Samuel R. Kaplan
year: 2007
title: The Dottie Number
doi: 10.1080/0025570X.2007.11953455
url: https://web.archive.org/web/20190504193821id_/https://www.maa.org/sites/default/files/Kaplan2007-131105.pdf
claim: The positive cosine fixed point has an odd rational pi series obtained by inverse Taylor expansion.
strata_touched:
  - D5/S3/Analytic/PowerSeries/DottieInverseSeries
license: citation-only
triage: anchor
---

<!-- GID: D5/L/AnalyticClosure/kaplan2007dottie -->
# The Dottie number and its inverse series

## Verified locator

Samuel R. Kaplan, “The Dottie Number,” Mathematics Magazine 80(1),
73–74, DOI 10.1080/0025570X.2007.11953455.

Archived primary PDF: <https://web.archive.org/web/20190504193821id_/https://www.maa.org/sites/default/files/Kaplan2007-131105.pdf>.
The two-page primary PDF has 70177 bytes and SHA256
`b37baf3288eaf6416721550615344264ab283ab1f07bfac7ace3da4c29ad80bc`.

## Mathematical scope

The article describes the inverse-Taylor construction of the odd rational
pi series and gives its first coefficients 1/4 and -1/768. It does not
supply the full formal-inverse coefficient identification, a domain or
radius argument, or absolute convergence at pi. The Lean development
supplies these obligations for the literal inverse of 2X+2arcsine(X).
No priority or originality claim is made for that completion.

## Formal correspondence

The rational coefficients of arcsine are zero in degree 2n and
choose(2n,n)/(4^n(2n+1)) in degree 2n+1. The formal inverse is the
PowerSeries.substInvOfIsUnit inverse of 2X+2arcsine(X), whose linear
coefficient is 4. Its real coefficients, including degree zero, are
identified with the Taylor coefficients of a single complex function.
The scalar composition correspondence used for this identification is
attributed separately to Miyahara Kō in
`Library/AnalyticClosure/miyahara2026scalarcomposition.md`.

This is a bibliographic reference; no article text or source code is copied.
