---
bibkey: gangloff2023various
authors: Silvère Gangloff; Pierre Guillon; Piotr Oprocha
year: 2023
title: Various questions around finitely positively expansive dynamical systems
doi: null
url: https://arxiv.org/abs/2310.17241v1
claim: Question 3.1 asks for strict finite positive-expansivity levels on the circle; Theorem 3.8 excludes finitely positively expansive interval systems.
strata_touched:
  - D5/S1/Dynamics/Shadowing/IntervalObstruction
  - D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness
license: citation-only
triage: anchor
---

# Various questions around finitely positively expansive dynamical systems

Question 3.1, Section 3, page 7 of arXiv:2310.17241v1, asks:

> Can we find, for every n ≥ 1, a positively (n + 1)-expansive map of the circle which is not positively n-expansive?

The repository's [full-circle theorem](../../Blueprint/D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.md)
proves that every continuous selfmap of the entire circle with a uniform
finite strict forward Bowen bound is positively expansive. Thus none of the
strict finite hierarchy levels requested in Question 3.1 exists. Its positive
expansivity scale may differ from the finite-bound scale. The theorem adds no
smoothness, invertibility or surjectivity hypothesis. The precise source
correspondence and comparison limits are in the
[circle problem dossier](../../Problems/gangloff-guillon-oprocha-circle-finite-positive-expansivity.md).
This circle proof is repository-derived; attribution of the question does not
attribute that proof to the paper or assert worldwide priority.

Theorem 3.8 states that no interval system is finitely positively expansive.
The repository gives a direct Lean proof for every nondegenerate compact
real interval and an equivalent formulation by arbitrarily large injective
families of all-time close forward orbits. These interval results are consumed
by the circle finite-positive-expansiveness proof; the known interval
obstruction is not claimed as a new discovery.

The direct proof uses exact interval pullbacks, monotone trapping and
coalescing fold histories. It does not assume the source theorem or use
mixing as an additional hypothesis.

## Verified locator

- https://arxiv.org/abs/2310.17241v1
- Question 3.1, Section 3, page 7.
- Theorem 3.8, Section 3.1, page 9.
