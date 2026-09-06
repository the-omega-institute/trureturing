---
bibkey: ponleitnerschichl2021exclusion
authors: Bettina Ponleitner and Hermann Schichl
year: 2021
title: Exclusion regions for parameter-dependent systems of equations
doi: 10.1007/s10898-021-01082-3
claim: Parameter-dependent interval inclusion and exclusion regions distinguish a small enclosure of a root from a larger neighborhood containing no other root.
strata_touched:
  - D5/S3/Quantum/Tomography/CayleyCoverAnalysis
  - D5/S3/Quantum/Tomography/HadamardResidualBarrier
license: citation-only
triage: anchor
---

# Parameter-dependent exclusion regions

The paper develops validated inclusion and exclusion regions for square
nonlinear systems with parameters. It distinguishes a tight root enclosure
from a larger neighborhood where that is the only root, and uses slope forms
and an approximate solution function to control a parameter box. Sections 2
through 4 provide the relevant analytic setting.

The MUB application reuses this distinction: a global base sublevel cover
enters large uniqueness guards; small root enclosures control nonedges. Its
separate matrix perturbation estimate sends every actual root for a nearby
Hadamard matrix into that base sublevel set. The concrete MUB neighborhood
and the graph obstruction are repository-specific calculations, not conclusions
of this paper.

Related primary sources are Duff and Lee, *Certified homotopy tracking using
the Krawczyk method*, arXiv:2402.07053v2 (ISSAC 2024), and Lee, *A priori bounds
for certified Krawczyk homotopy tracking*, arXiv:2512.01355 (2025). These support
certified path following and step scheduling. Following a finite collection of
known paths is separate from proving that no additional roots exist outside
those paths.

## Verified locators and scope

- https://doi.org/10.1007/s10898-021-01082-3
- https://arxiv.org/abs/2402.07053
- https://arxiv.org/abs/2512.01355

The publisher HTML for the 2021 article and arXiv metadata/abstracts for both
tracking papers were checked on 2026-09-06. No uninspected theorem number or
proof detail from the two tracking papers is assumed in the formal source.
