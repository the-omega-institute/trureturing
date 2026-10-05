---
bibkey: baake2011peanobaker
authors: Michael Baake; Ulrike Schlaegel
year: 2011
title: The Peano-Baker series
doi: 10.1134/S0081543811080098
claim: The time-ordered Peano-Baker series converges on compact intervals and gives the unique solution of continuous finite-dimensional linear systems.
strata_touched:
  - D5/S3/Quantum/Transport/MatrixUnitDyson
license: citation-only
triage: anchor
---

# Ordered series for continuous matrix paths

Proceedings of the Steklov Institute of Mathematics 275 (2011), 167-171.
DOI: https://doi.org/10.1134/S0081543811080098
Public author version: https://arxiv.org/abs/1011.1775
Readable version: https://arxiv.org/html/1011.1775v3

Section 2, equations (3)-(5), gives the actual Volterra equation, ordered
integral series, and recursive terms with the latest matrix acting on the left.
Lemma 1 establishes the derivative of a recursive term. Theorem 1 proves
compact convergence by a factorial majorant using a compatible matrix norm.
Section 3 identifies the series with the unique fundamental solution.
These are classical antecedents of the generic branch of constructive_transport.

The repository declaration realizes these mechanisms using Bochner integrals,
an independent closed-simplex integral with a noncommutative List.prod, and
the Euclidean operator norm. It covers nonnegative horizons, within derivatives
at both endpoints, and a finite physical index type that may be empty.
It then applies the repository's computed matrix-unit generator to obtain
unitarity and transport of every logical matrix unit. This note does not
attribute that full combined telescope or the matrix-unit averaging formula
to this paper, and does not claim mathematical priority for the series method.

## Verified locator

The arXiv abstract identifies the title, both authors and journal reference.
The readable author version contains equations (3)-(5), Lemma 1, Theorem 1,
and the uniqueness discussion in Section 3. Crossref identifies the journal
DOI and title above. The citation does not supply a Lean proof dependency.
