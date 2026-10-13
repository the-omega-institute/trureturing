# The actual five-mode Fisher immersion

## Abstract

The positive five-mode simplex has exact four-dimensional affine coordinates and a smooth square-root immersion whose Euclidean pullback is its Fisher form.

Four free coordinates q give the five probabilities p = (1 - sum(q), q_0, q_1, q_2, q_3). The chart domain is exactly the set on which all five probabilities are positive. Every positive mass-one law has exactly one such coordinate vector. A tangent direction u is lifted to (-sum(u), u_0, u_1, u_2, u_3), so this is the entire four-dimensional mass-conserving tangent space.

**Theorem 1.1 (Smooth sphere immersion and exact Fisher pullback).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion.five_mode_fisher_chart_immersion`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion.five_mode_fisher_chart_immersion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chart domain is open. The map p_s to 2 sqrt(p_s) is smooth there, its squared coordinates sum to four, and its actual Frechet derivative sends the lifted direction u_s to u_s / sqrt(p_s). This derivative is injective. The ordinary coordinate pairing of the two derivative images is exactly the existing Fisher form, sum(u_s v_s / p_s). Therefore that form is strictly positive on every nonzero free direction.

The proof constructs the affine chart and its unique inverse, uses the Mathlib square-root derivative on the positive domain, and cancels the square roots in the pullback pairing. Injectivity of the tangent lift and positivity of a nonzero squared coordinate prove positive definiteness.

Square-root sphere coordinates for the categorical Fisher-Rao metric are classical information geometry, not a novelty claim. The project already states this construction in HIDDEN Proposition C-4.6 and the thermodynamic-action volume Section 10. Their cited classical background is Frank Nielsen, An elementary introduction to information geometry, arXiv:1808.08271v2, and its expanded Entropy 22(10), 1100 (2020), doi:10.3390/e22101100. This module supplies the actual compiled five-mode affine chart, Frechet derivative and exact pairing; no upstream Fisher-simplex Lean proof was located in the bounded repository and pinned-Mathlib search.

This theorem supplies the affine chart and immersion. The actual smooth tangent-bundle metric is constructed separately in FiveModeFisherMetric, consuming this theorem. The induced path-distance structure is supplied by Mathlib and is not redelivered as a wrapper here. Neither module supplies a total map from all 5040 arithmetic parameters to the simplex, the global Robin inequality, or RH. A mixed finite-difference sign is not Riemannian curvature.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion.five_mode_fisher_chart_immersion`
- Dependency: [D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates](FiveModeMixedCoordinates.md)
