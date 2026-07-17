---
bibkey: chatland1949euclidean
title: On the Euclidean algorithm in quadratic number fields
doi: 10.1090/S0002-9904-1949-09315-1
claim: The ring of integers of Q(sqrt(5)) admits Euclidean division for the absolute field norm.
strata_touched:
  - D5/S0/Carrier/Euclidean
license: citation-only
triage: anchor
---

# On the Euclidean Algorithm in Quadratic Number Fields

H. Chatland defines a quadratic field as Euclidean when, for algebraic integers
`alpha` and nonzero `beta`, there is an algebraic integer `gamma` satisfying
`|N(alpha - beta * gamma)| < |N(beta)|`. The paper explicitly lists `m = 5`
among the positive square-free values for which this algorithm is known to
exist. The repository's `GoldenInt` is the integral-basis model of this ring of
integers, `Z[phi]`.

The paper attests the theorem and its norm inequality. The deterministic
nearest-coordinate quotient, the `5/16` estimate, and the exact Lean
`EuclideanDomain` construction are the repository's formal proof choices.

## Search log

- Queried Crossref for `The Euclidean algorithm in algebraic number fields`.
  Crossref returned Chatland's title, author, year, and DOI
  `10.1090/S0002-9904-1949-09315-1`.
- Downloaded the six-page article from the AMS journal archive, rendered its
  first page, and checked both the page image and extracted text. The
  introduction gives the strict absolute-norm remainder inequality, and the
  previous-results section includes `5` in the positive Euclidean list.

## Verified locator

- DOI: https://doi.org/10.1090/S0002-9904-1949-09315-1
- AMS PDF: https://www.ams.org/journals/bull/1949-55-10/S0002-9904-1949-09315-1/S0002-9904-1949-09315-1.pdf
