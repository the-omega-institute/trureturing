---
bibkey: koshy2001fibonacci
authors: Thomas Koshy
year: 2001
title: Fibonacci and Lucas Numbers with Applications
doi: 10.1002/9781118033067
claim: Golden-ratio identities, Fibonacci matrices, and exact Fibonacci formulas.
strata_touched:
  - D5/S0/Carrier/GoldenRatio
  - D5/S1/Scale/FibonacciEigen
  - D5/X_Frontier/Conjectures/ZeckendorfNormSign
license: citation-only
triage: anchor
---

# Fibonacci and Lucas Numbers with Applications

Thomas Koshy's 2001 Wiley volume is the literature anchor for the elementary
golden-ratio identities and the Fibonacci matrix and formula material used by
the two formal declarations.

## Search log

- 2026-07-16: Queried NyxID/Tavily for `Thomas Koshy Fibonacci and Lucas
  Numbers with Applications DOI`. The Wiley result identified the 2001 title,
  author, publication date, online ISBN, and DOI `10.1002/9781118033067`.
- 2026-07-16: Queried `Koshy 2001 Fibonacci and Lucas Numbers with
  Applications Binet formula Fibonacci matrices golden ratio`. Google Books
  exposed chapters 20-21 on the golden ratio and chapters 32-33 on Fibonacci
  matrices and determinants; its searchable index also returned Binet's
  formula and matrix entries.
- 2026-07-16: Queried `Fibonacci Q-matrix eigenvalues golden ratio book Koshy`
  and `golden ratio phi squared phi plus one reciprocal conjugate Koshy`.
  Results independently exposed the standard matrix eigenpairs, the quadratic
  identity, and the negative-reciprocal conjugate used in the Lean statements.
- 2026-07-16: The first three proxy attempts serialized the JSON object as a
  string and received HTTP 422. Reissuing the same queries with JSON supplied
  on stdin produced the results above; no bibliographic conclusion was drawn
  from the failed requests.
- 2026-08-17: Searched the D5 Lean source by statement shape for combinations
  of `betaGolden`, `norm`, least Zeckendorf index, parity, and sign. No exact
  declaration was found; one broad-regex hit in `RationalSpectrum` was
  unrelated.
- 2026-08-17: Searched the pinned Mathlib source for Zeckendorf declarations
  combined with parity, norm, conjugate, or sign. The combined query exited 1
  with no match.
- 2026-08-17: Queried Loogle for `Nat.zeckendorf`. Its seven results were the
  standard representation, canonicality, decoding, and uniqueness API; none
  related least-index parity to a quadratic norm sign.
- 2026-08-17: Posted the exact LeanSearch query `Zeckendorf representation
  least occupied index parity determines sign of the golden conjugate norm`.
  Results covered the standard Zeckendorf API and Binet formula, with no exact
  or equivalent sign theorem.
- 2026-08-17: Queried arXiv for `all:"Zeckendorf" AND all:"golden ratio" AND
  all:"conjugate"`; the API reported `totalResults=0`. This finite search
  supports only a `suspected-novel` classification, not established novelty.

## Verified locator

- Wiley: https://onlinelibrary.wiley.com/doi/book/10.1002/9781118033067
- Google Books: https://books.google.com/books?id=1iDKKceqD2sC
