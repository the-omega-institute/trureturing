---
bibkey: penrose1955generalized
authors: R. Penrose
year: 1955
title: A generalized inverse for matrices
doi: 10.1017/S0305004100030401
claim: Every finite complex rectangular matrix has a unique generalized inverse characterized by the four Penrose equations.
strata_touched:
  - D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse
license: citation-only
triage: anchor
---

# A generalized inverse for matrices

Penrose, Mathematical Proceedings of the Cambridge Philosophical Society
51(3), July 1955, pages 406-413. The publisher-supplied abstract describes
existence and uniqueness for every possibly rectangular complex matrix,
characterized by equations. This note attributes that classical result;
it does not claim that the repository invented the inverse.

The Lean construction is an attributed Apache-2.0 source port from
AIQ-Kitware/aiq-dkps-formalization, immutable commit
20461e477e1ae464d6abac1dade3188c29109b8c,
ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean and selected
prerequisites from Singular/System.lean. Its full license, author notices,
compatibility modifications and retirement condition are in the Lean file.
It constructs the inverse using a right singular basis and derives all four
equations and uniqueness. The repository's finite-synthesis and canonical
Nyman-Beurling distance theorems are downstream specializations.

## Verified locator

- DOI: https://doi.org/10.1017/S0305004100030401
- Crossref record queried successfully on 2026-09-06 at
  https://api.crossref.org/works/10.1017%2FS0305004100030401
  verified author, title, July 1955 date, volume 51, issue 3, pages 406-413,
  DOI and the publisher-supplied abstract. No internal theorem number is claimed.

## Formal source

- https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/20461e477e1ae464d6abac1dade3188c29109b8c/ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean
- https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/20461e477e1ae464d6abac1dade3188c29109b8c/ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean
