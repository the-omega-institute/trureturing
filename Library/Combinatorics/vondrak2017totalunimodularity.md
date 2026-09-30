---
bibkey: vondrak2017totalunimodularity
authors: Jan Vondrák; Richard Pang (scribe)
year: 2017
title: "MATH233B: Polyhedral techniques in combinatorial optimization, Lecture 3"
doi: null
url: https://theory.stanford.edu/~jvondrak/MATH233B-2017/lec3.pdf
claim: "Lemma 10: the signed vertex-edge incidence matrix of a directed graph is totally unimodular."
strata_touched:
  - D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity
license: citation-only
triage: anchor
---

# Vondrák, signed incidence matrices and total unimodularity

Jan Vondrák's MATH233B Lecture 3, dated January 17, 2017 and written by Richard Pang, defines the signed incidence matrix with one `+1` endpoint, one `-1` endpoint, and zero elsewhere. Lemma 10 states that this directed-graph matrix is totally unimodular. Its proof uses the induction in the lecture's Lemma 3: expand a sparse column, and otherwise use the zero sum of the rows.

The repository formalization uses the endpoint presentation `tail head : E → V` rather than a simple directed-graph structure. This admits arbitrary parallel labels and loops; a loop column cancels to zero. The theorem is literature-attested, not claimed as original.

## Verified locator

- URL: https://theory.stanford.edu/~jvondrak/MATH233B-2017/lec3.pdf
- Locator: Lecture 3, printed page 3, Lemma 10; the signed incidence definition appears immediately before it.
- Secondary comparison: Kevin Cheung, MATH5801, Proposition 7.1, which gives the one-positive/one-negative-per-column criterion.
