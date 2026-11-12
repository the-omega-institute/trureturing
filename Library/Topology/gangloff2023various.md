---
bibkey: gangloff2023various
authors: Silvère Gangloff; Pierre Guillon; Piotr Oprocha
year: 2023
title: Various questions around finitely positively expansive dynamical systems
doi: 10.1016/j.topol.2025.109597
url: https://arxiv.org/abs/2310.17241v1
claim: Question 3.1 asks for strict finite positive-expansivity levels on the circle; Theorem 3.8 excludes finitely positively expansive interval systems; the repository also proves the obstruction for every nondegenerate compact metric standard dendroid, within the scope of Question 3.2.
strata_touched:
  - D5/S1/Dynamics/Shadowing/IntervalObstruction
  - D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness
  - D5/S1/Dynamics/Shadowing/DendriteObstruction
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

The repository's [all-dendroid theorem](../../Blueprint/D5/S1/Dynamics/Shadowing/DendriteObstruction/AllDendroid.md)
proves that every continuous self-map of every nondegenerate compact metric
standard dendroid fails finite positive expansivity. Here the standard
dendroid structure is arcwise connectedness and hereditary unicoherence;
local connectedness, finite branching and uniform arc packing are not
additional assumptions. The map need not be invertible or surjective.
Precisely, for every positive real scale and every natural number m at least
two, there are exactly m distinct points whose joint image under each
iterate has diameter strictly below that scale at every natural time,
including time zero. This is a complete obstruction for the dendroid class;
it does not settle the entire one-dimensional classification in Question 3.2.

The static small-opening theorem supplies the separate opening hypothesis
of the dynamic minimal-invariant-set argument. It gives, inside every
nondegenerate subcontinuum and at every positive scale, a compact connected
subset whose nonempty relative open complement has diameter strictly below
that scale. The static theorem is classical: Krasinkiewicz and Minc,
*Continua and their open subsets with connected complements*, Fundamenta
Mathematicae 102 (1979), 129–136,
[DOI 10.4064/fm-102-2-129-136](https://doi.org/10.4064/fm-102-2-129-136).
Heath and Nall, *Centers of a dendroid*, Fundamenta Mathematicae 189 (2006),
173–183, [DOI 10.4064/fm189-2-6](https://doi.org/10.4064/fm189-2-6),
state the small co-connected-open property on the read page 180.
The Lean package proves and consumes this static input through
ProperExpansion, CoconnectedOpening and TentObstruction; it does not assume
it as an axiom or claim it as a new static theorem.

The GGO journal DOI
[10.1016/j.topol.2025.109597](https://doi.org/10.1016/j.topol.2025.109597)
is confirmed bibliographic metadata. The question and theorem locators here
refer to the read arXiv v1. The final GGO article body and the Artigue article
body associated with [DOI 10.1016/j.topol.2026.110006](https://doi.org/10.1016/j.topol.2026.110006)
remain unavailable for comparison. No worldwide originality or priority
claim follows from this repository result.

## Verified locator

- https://arxiv.org/abs/2310.17241v1
- Question 3.1, Section 3, page 7.
- Theorem 3.8, Section 3.1, page 9.
