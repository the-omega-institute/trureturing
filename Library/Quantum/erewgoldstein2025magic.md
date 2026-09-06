---
bibkey: erewgoldstein2025magic
authors: Muhammad Erew and Moshe Goldstein
year: 2025
title: 'Extremizing Measures of Magic on Pure States by Clifford-stabilizer States'
doi: 10.48550/arXiv.2512.19657
claim: The ququint state and Wigner convention are taken from the paper; the constrained direction analysis is left open there.
strata_touched:
  - D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry
license: citation-only
triage: anchor
---

# Ququint Critical Geometry

## Verified locator

DOI 10.48550/arXiv.2512.19657, https://arxiv.org/abs/2512.19657 and
https://arxiv.org/html/2512.19657v2. Appendix E, equation (E.3a), gives
the state (1,1,zeta^3,1,zeta^2)/sqrt(5). Equation (2.16) gives the
phase-point convention after renaming the paper's (p,q) to (q,p).
Section 4.4.2, after (4.55), leaves the mana behavior for the constrained
variations to the reader; the last row of Table 2 is undetermined.

The saved full text and abstract were read in the preceding implementation
attempt and inspected again for this continuation. PR #5657 records the
independent source check. The current Lean development certifies the exact
geometry and vanishing first variation. QuquintStrictDecrease proves the
exact normalized change and strict mana decrease along every nonzero
direction in the specified constrained tangent family. This is a local
repository result, not a claim that the source paper contains that proof.

This lane does not claim a general solution of mana extremisation, other
dimensions, other critical points, that Claim C is the authors' verbatim
conjecture, or global novelty beyond the recorded search.
