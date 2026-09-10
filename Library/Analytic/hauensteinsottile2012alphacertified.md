---
bibkey: hauensteinsottile2012alphacertified
authors: Jonathan D. Hauenstein and Frank Sottile
year: 2012
title: Algorithm 921: alphaCertified: Certifying Solutions to Polynomial Systems
doi: 10.1145/2331130.2331136
claim: Smale alpha-theory can certify approximate nonsingular solutions of polynomial systems, with implementations supporting exact rational arithmetic and arbitrary-precision arithmetic.
strata_touched:
  - D5/S3/Quantum/Tomography/CayleyCoverAnalysis
license: citation-only
triage: anchor
---

# alphaCertified and exact isolated-root certification

Hauenstein and Sottile implement Smale alpha-theory for certification of
isolated roots of square polynomial systems. The relevant methodological point
for the MUB-six lane is the separation between discovery and certification:
approximate roots may be found numerically, while exact rational or
arbitrary-precision calculations certify convergence to genuine nonsingular
solutions.

The strict-X common-unbiased equations play a similar role after signed Cayley
parameterization. The current repository uses interval/Krawczyk-style boxes
rather than alpha-theory constants, because the same box arithmetic can both
exclude regions and certify uniqueness. The two approaches are complementary:
alpha-theory is a natural independent checker for isolated algebraic roots at
sample parameter points, while the interval cover controls the entire compact
phase domain and parameter neighborhoods.

Neither method by itself proves that no additional roots exist outside the
certified neighborhoods. The new `root_mem_iUnion_of_uniform_residual_gap`
interface isolates precisely that missing global obligation: a positive
residual gap on the complement, stable under parameter perturbation.

## Verified locator

- DOI: https://doi.org/10.1145/2331130.2331136
- arXiv: https://arxiv.org/abs/1011.1091
