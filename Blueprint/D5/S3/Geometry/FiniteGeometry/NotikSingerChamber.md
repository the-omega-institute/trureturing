# Largest-gap cuts and real Golomb chambers

## Abstract

A cyclic perfect difference set cut at a largest gap gives the unique shortest ruler in its normalized real chamber.

**Definition 1.1 (Unique labelled cyclic differences).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.CyclicPerfectDifference`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.CyclicPerfectDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For natural numbers m and N and natural marks x indexed by Fin (m + 1), every natural d with 0 < d < N has exactly one ordered pair (i, j) of distinct indices whose signed integer difference x(j) − x(i) is congruent to d modulo N in Int.ModEq. The labels and their order are part of the witness.

**Definition 1.2 (The normalized real chamber).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.Chamber`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.Chamber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For natural reference marks x and real marks y on the same Fin (m + 1), the chamber requires y(0) = 0 and y(j) − y(i) ≥ 1 for every i < j. For every i < j and k < l, whenever the reference natural distance x(j) − x(i) is strictly smaller than x(l) − x(k), the corresponding real distances satisfy y(j) − y(i) + 1 ≤ y(l) − y(k).

**Theorem 1.3 (Unique shortest ruler after a largest-gap cut).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Let m > 0, let x be strictly increasing natural marks on Fin (m + 1) with x(0) = 0, and write L for the last mark. Let G > 0 be a natural number with every adjacent gap of x at most G. Assume CyclicPerfectDifference for x modulo L + G, so G is a largest cyclic gap and ties are allowed. Equal ordinary distances for i < j and k < l imply (i, j) = (k, l). The real cast of x belongs to its chamber. Every real y in that chamber whose last mark is at most L equals x pointwise after casting.

Each positive residue below G occurs as a forward distance because a wrapped difference is at least G. Induction using the chamber inequalities bounds every retained gap below by its reference value. The markwise deviations are therefore nondecreasing, and the two endpoint conditions force them all to be zero.

This repository derivation addresses Notik’s §7 conjecture through the cyclic perfect difference property. It applies to every positive m and G satisfying the hypotheses, including the source’s Singer rulers for all prime powers, unit multipliers and largest-gap cuts once their cyclic perfect difference property is supplied. The theorem takes that property as a hypothesis and compares lengths within the specified chamber.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.Chamber`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.CyclicPerfectDifference`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result`
