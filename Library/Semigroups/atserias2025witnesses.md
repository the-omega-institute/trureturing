---
bibkey: atserias2025witnesses
authors: Albert Atserias and Phokion G. Kolaitis
year: 2025
title: "Consistency Witnesses for Annotated Relations"
doi: 10.1145/3749116.3749118
url: https://sigmodrecord.org/publications/sigmodRecord/2506/pdfs/03_Principles_Atserias.pdf
claim: "For positive commutative monoids, Theorem 1 equates binary transportation, finite transportation and inner consistency; Section 6 constructs witnesses fiberwise from transportation matrices."
strata_touched:
  - D5/S3/Combinatorics/Transportation/FiniteFiberTransport
license: citation-only
triage: anchor
---

# Finite transportation and consistency witnesses

## Verified locator

- DOI: https://doi.org/10.1145/3749116.3749118
- Publisher PDF: https://sigmodrecord.org/publications/sigmodRecord/2506/pdfs/03_Principles_Atserias.pdf

Albert Atserias and Phokion G. Kolaitis, SIGMOD Record 54 (2), June 2025.
The publisher text was read for the definitions in Section 2, Theorem 1 in
Section 4, the fiber construction in Section 6, and the questions in Section 8.

## Mathematical scope

A positive monoid in this paper is a commutative monoid whose zero has no
nonzero summands: if x+y=0, then x=y=0. Individual weights may be zero.
Section 4 defines transportation for positive integer dimensions. Theorem 1
equates its binary case with all finite positive dimensions and with inner
consistency of annotated relations. Section 6 solves a transportation problem
for each common projected tuple and combines these solutions into a consistency
witness.

The Lean result uses the same additive equations, with arbitrary finite row
and column types, including empty types, and an arbitrary label type.
Conicality handles the empty cases. Conversely, a two-element row type and
empty column type recover conicality, and two two-element types with one
common label recover binary refinement. Thus positivity is part of the
equivalence rather than an additional premise. The trivial monoid is included.
The finite-family splitting and matrix construction formalize known
transportation mathematics; no mathematical novelty is claimed.

The largest-support classification discussed in Section 8 concerns inclusion
of supports of consistency witnesses. It is distinct from pointwise maximum
weights and from uniqueness of a witness. The transportation equivalence
does not settle that classification.
