---
bibkey: binarysubspace2026nonradical
authors: Public binary-subspace-orthogonality research workspace; note without individual byline
year: 2026
title: "Retaining only lines and totally isotropic subspaces"
doi: null
url: https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/notes/nonradical-line-retraction.md
claim: "The full nonzero-subspace orthogonality graph retracts onto its induced graph of lines and pairwise totally isotropic subspaces in every dimension."
strata_touched:
  - D5/S3/Combinatorics/Orthogonality/NonradicalLineRetraction
license: citation-only; no unified research-material reuse license selected
triage: anchor
---

# Nonradical-line retraction

## Verified locator

https://github.com/the-omega-institute/binary-subspace-orthogonality/blob/9f065627944f30fe7b56e6ec0fb1025d3bb5a7ce/notes/nonradical-line-retraction.md

The source note has SHA256
`0b02086dca942f21bff16dd5453ca23ae46983c0547f4c37c13f63e7f5bbfb1d`.
It is a public research note with no individual byline, DOI or asserted peer review.
The workspace README names Haobo Ma, Reza Nikandish and Wenlin Zhang; that
workspace attribution does not determine the authorship of this particular note.

## Mathematical correspondence

The formal ambient space is `Fin n → ZMod 2` with the existing
`standardCoordinatePairing`. The existing `NikandishClique.Vertex` includes
every nonzero submodule, including the whole space. Retention means dimension
one or bilinear vanishing on every pair of vectors in the submodule.

The original proof constructs a contained nonradical line for each vertex that
is not retained. Containment preserves orthogonality. Nonradicality prevents
the two images of an edge from becoming equal. Retained vertices are fixed.
The mathematical statement permits isotropic image lines and covers dimension
zero without an inhabited-target assumption. Coloring transport is an application
of existing graph-homomorphism APIs, rather than an additional named theorem.
The note's finite counts, solver descriptions and exact-coloring questions are
outside this formal statement.

## Rights boundary

The same revision's `RIGHTS.md` has SHA256
`bad872397d230fdb2460961682b36cc773c3a871411c63f032f4b21fa7b0b3e3`.
It states that a unified license for new research materials has not been selected.
This note supplies attribution and mathematical correspondence. The Lean proof
is independently written; no source code or verbatim research note is reproduced.
The Apache license of the separately imported `formal/NikandishClique.lean`
does not establish a license for this research note.
