# The five-mode Fisher tangent metric

## Abstract

The actual four-dimensional affine chart of the positive five-mode simplex supports the smooth Fisher metric on its tangent bundle.

The base is the open subset of four real coordinates giving p = (1 - sum(q), q_0, q_1, q_2, q_3) with all five entries positive. The previously proved affine chart gives exactly one such q for every positive mass-one five-mode law. Mathlib equips this open subset with its genuine smooth manifold and tangent-bundle structures.

**Definition 1.1 (The constructed smooth tangent-bundle metric).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherRiemannianMetric`

*Formalization.* `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherRiemannianMetric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The metric object is a ContMDiffRiemannianMetric on that actual tangent bundle. Its continuous bilinear form is the weighted sum of the rank-one forms of the lifted probability coordinates: g_q(u,v) = sum_s lift(u)_s lift(v)_s / p_s. It is symmetric and strictly positive on nonzero directions, and its metric unit balls are bounded for the pre-existing tangent topology.

Positive definiteness reuses the square-root Fisher immersion. Each probability is at most one because the positive entries sum to one. Each free-coordinate square is therefore bounded by the quadratic Fisher form, so a metric unit ball lies in the ordinary coordinate norm unit ball. The reciprocal probabilities are smooth. All affine chart transitions have identity derivatives; reading the metric in the genuine iterated hom-bundle trivialization therefore gives the same smooth family of continuous bilinear maps.

This is the classical categorical Fisher-Rao metric, with square-root sphere interpretation already stated in the project's HIDDEN C-4.6 and thermodynamic-action Section 10. The classical background is Nielsen's An elementary introduction to information geometry, arXiv:1808.08271v2 and its expanded Entropy 22(10), 1100 (2020), doi:10.3390/e22101100. No novelty claim is made for the metric. The new library bridge is the actual constructed Mathlib object for the project's five-mode law.

The construction does not identify arithmetic finite differences with a Levi-Civita curvature tensor, does not provide a total 5040/RH parameter map, and does not settle the global Robin inequality or RH.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.fisherRiemannianMetric`
- Dependency: [D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion](FiveModeFisherImmersion.md)
