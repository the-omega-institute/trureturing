---
bibkey: cirelson1980quantum
authors: B. S. Cirel'son
year: 1980
title: Quantum generalizations of Bell's inequality
doi: 10.1007/BF00417500
claim: The CHSH quantum expectation is bounded by two times square root two, and the bound is attained by a two-qubit realization.
strata_touched:
  - D5/S3/QuantumBounds/TsirelsonTightness
license: citation-only
triage: anchor
---

# Quantum generalizations of Bell's inequality

Cirel'son's paper is the literature anchor for the sharp quantum CHSH bound
conventionally called Tsirelson's bound. The repository declaration specializes
that classical result to one explicit four-by-four CHSH operator: it proves that
the real trace expectation over positive-semidefinite trace-one matrices has
greatest value `2 * sqrt 2`.

The exact Lean `IsGreatest` packaging, the repository's named Pauli matrices and
Bell density, and the proof that transports matrix order through a positive
trace pairing are not attributed to the paper. The cited result supplies the
bound and its classical provenance; the formal declaration supplies this fixed
finite-dimensional realization.

## Search log

- 2026-08-15: Crossref DOI metadata was queried directly. It identifies B. S.
  Cirel'son, the exact title, *Letters in Mathematical Physics* 4(2), 93-100
  (1980), DOI `10.1007/BF00417500`.
- 2026-08-15: The Springer landing page was read. Its abstract states that
  quantum correlations obey weaker inequalities of Bell type and that the
  paper proves particular inequalities of this kind.
- 2026-08-15: The pinned mathlib source
  `Mathlib.Algebra.Star.CHSH` was read. It contains
  `tsirelson_inequality`, the upper-bound theorem used by the Lean declaration.
- 2026-08-15: The publisher records the article as closed access. A direct
  text-mining PDF request returned HTML rather than the article, so no equation
  number or claim about the paper's exact notation is made here.

## Verified locator

- DOI: https://doi.org/10.1007/BF00417500
- Crossref record: https://api.crossref.org/works/10.1007/BF00417500
