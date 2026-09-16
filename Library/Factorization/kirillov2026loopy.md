---
bibkey: kirillov2026loopy
authors: Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob
year: 2026
title: "The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry"
doi: null
url: https://arxiv.org/abs/2609.07728v1
claim: "Definition 1.1 and Proposition 2.1 give the ordinary Loopy recursion and its choice independence; Problem 11.4 asks whether it determines the degree sequence for arbitrary graphs with loops included."
strata_touched:
  - D5/S3/Factorization/Combinatorics/LoopyEvaluator
  - D5/S3/Factorization/Combinatorics/LoopyDegreeSequence
license: citation-only
triage: anchor
---

# The ordinary Loopy polynomial and degree sequences with loops

The cited source is arXiv:2609.07728v1, published September 7, 2026. Definition
1.1 gives deletion-contraction for a nonloop, multiplication under disjoint
union and the looped one-vertex base value. Proposition 2.1 proves that the
recursion is independent of the choices used to compute it. The repository's
labelled evaluator refines these laws to finite vertex sets, lists of edge
occurrences and an accumulated-loop function. Lists retain parallel edges;
contraction of a selected nonloop keeps that occurrence as one accumulated
loop.

Section 6.5, including Remark 6.17 and Lemma 6.18, supplies refined-degree
context. It does not prove the repository's substitution x_r = [2r+1], nor
does it prove that the ordinary Loopy polynomial recovers degrees when loops
are present. The paper distinguishes the refined invariant from the ordinary
one and states the latter question explicitly as Problem 11.4:

> Does L_G determine the degree sequence of an arbitrary graph G, loops included?

The repository proves the equality-kernel form: for any two independently
encoded finite undirected multigraphs, validity and equality of their ordinary
Loopy polynomials imply equality of their complete actual degree multisets.
There is no equal-order premise. Parallel edges, loops counted twice, isolates,
disconnected graphs and empty graphs are all included.

## Verified locator

The caller read https://arxiv.org/abs/2609.07728v1 and the public arXiv HTML at
Definition 1.1, Proposition 2.1,
section 6.5 (Remark 6.17 and Lemma 6.18) and Problem 11.4. Its SHA-256 is
`e38f48ed00c59fd2a80f59395a3b08c6a42ea0ead467ac5cce029b3886394332`.
The downloaded PDF has SHA-256
`f3d4ae846384717ecce1c31261f021f172dad47443c7dd635d1d15b64ddd8f12`.
The caller read the title on PDF page 1, the ordinary/refined distinction on
PDF pages 33--34, and the exact question on PDF page 63. PDF text extraction
drops the refined-L typography, so the corresponding HTML MathML and alt text
supply that distinction. The metadata source lists
Anatol Kirillov, Gleb Nenashev, Boris Shapiro and Arkady Vaintrob, category
math.CO, and publication time `2026-09-07T16:36:46Z`.

The supplied bounded search covered source v1 and an exact-phrase arXiv query;
supplementary Crossref, Semantic Scholar, Google and Bing responses did not
establish absence of prior work. The source itself presents Problem 11.4 as
open in v1. Worldwide priority remains `ASSUMED-UNVERIFIED`; this note makes no
global novelty claim.
