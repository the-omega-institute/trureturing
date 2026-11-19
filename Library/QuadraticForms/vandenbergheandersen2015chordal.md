---
bibkey: vandenbergheandersen2015chordal
authors: Lieven Vandenberghe; Martin S. Andersen
year: 2015
title: Chordal Graphs and Semidefinite Optimization
doi: 10.1561/2400000006
url: https://www.seas.ucla.edu/~vandenbe/publications/chordalsdp.pdf
claim: Theorem 10.1 characterizes real positive semidefinite completability of chordal-pattern partial matrices by positivity of all clique blocks.
strata_touched:
  - D5/S3/QuadraticForms/ChordalPsdCompletion
license: citation-only
triage: anchor
---

## Verified locator

- DOI: https://doi.org/10.1561/2400000006
- Full text: https://www.seas.ucla.edu/~vandenbe/publications/chordalsdp.pdf
- Theorem 10.1, printed page 356: a chordal-pattern partial real symmetric
  matrix has a positive semidefinite completion exactly when every clique
  principal block is positive semidefinite.
- Printed page 360, equations (10.9)–(10.11): singular clique blocks are allowed;
  the range and pseudoinverse conditions replace an invertible-block argument.

## Formal correspondence

`ChordalPsdCompletion.exists_posSemidef_completion` proves the existence
implication for every finite vertex type, including the empty carrier and
arbitrary universes. A full real table represents the partial data; only its
diagonal and graph-edge entries are preserved. Symmetry on specified entries
comes from the clique positivity hypothesis. No rank bound, positive
definiteness, connectedness, invertibility or nonedge constraint is imposed.

The proof uses the repository's simplicial elimination theorem, pinned
Mathlib's finite PSD Gram factorization and Gram positivity, and the original
real equal-Gram contraction in `WeightedGramContraction`. It recursively
constructs a compatible family, with one residual coordinate at each step.
This is a formal proof of established mathematics, not a claim of mathematical
originality. This note cites the article and grants no redistribution licence.
