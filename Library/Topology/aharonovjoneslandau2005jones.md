---
bibkey: aharonovjoneslandau2005jones
authors: Dorit Aharonov, Vaughan Jones, Zeph Landau
year: 2005
title: A polynomial quantum algorithm for approximating the Jones polynomial
doi: null
url: https://arxiv.org/abs/quant-ph/0511096v2
claim: The Artin presentation, Temperley–Lieb representation, writhe correction and path-model Markov trace provide classical sources for the algebraic bridge.
strata_touched:
  - D5/S3/Quantum/Algebra/Knot
license: citation-only
triage: anchor
---

# Artin representation and path-model trace

The primary version is arXiv:quant-ph/0511096v2. Definition 2.5 gives the
Temperley–Lieb braid representation. Lemma 2.2 and equation (4) relate the
trace normalization and writhe correction to the Jones construction.
Definitions 3.2–3.3 and Claim 3.6 supply the particular line-graph path
model and its Markov trace law. These are classical inputs, not new
mathematical claims of the repository.

The repository's weighted path suppliers work with arbitrary finite
symmetric adjacency and positive Perron data; this general source scope
is proved in those suppliers and is not attributed to the paper's
particular line-graph model. WeightedPathArtinRepresentation consumes
both local Temperley–Lieb directions, the weighted trace, and literal
path-append naturality to construct the actual finite Artin quotient,
its representation by units, strand inclusion and integer writhe.

Under the repository convention rho = A^-1 I + A delta P with
delta = -A^2 - A^-2, the positive and negative stabilization trace factors
are -A^-3/delta and -A^3/delta. The proved normalization is
delta^(n-1)(-A^3)^w tau(rho(beta)). Conjugation and both stabilization
signs generate the algebraic Markov relation independently of that
value. The checked invariance proof makes the value descend to its
quotient.

The algebraic quotient is not identified with geometric link isotopy.
A closure map, the geometric Markov theorem, convention-preserving
Jones identification, Laurent integrality and the ABF modulo-3 target
remain separate proof obligations. The cited quantum algorithm and
its complexity guarantees are not implemented by this algebraic bridge.

## Verified locator

Primary source: https://arxiv.org/abs/quant-ph/0511096v2.
Primary HTML: https://arxiv.org/html/quant-ph/0511096v2.
Inspected scope: Definition 2.5, Lemma 2.2/equation (4), and
Definitions 3.2–3.3/Claim 3.6; no geometric closure identification claimed.
