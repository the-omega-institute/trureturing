# Kraus–Simanek Conjecture 2.1

## Abstract

Polynomial content has no maximizer on suitable unit-area polygons.

**Definition 1.1 (claim).**

$$claim \equiv \forall N: \mathbb{N}, \exists n: \mathbb{N}, \neg (\exists P: Set\left(\mathbb{C}\right), (IsPolygonRegion\left(n\right)\left(P\right)) \land ((volume\left(P\right) = 1) \land (\forall Q: Set\left(\mathbb{C}\right), (IsPolygonRegion\left(n\right)\left(Q\right)) \Rightarrow ((volume\left(Q\right) = 1) \Rightarrow (rhoN\left(N\right)\left(Q\right) \le rhoN\left(N\right)\left(P\right))))))$$

*Formalization.* `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.claim` (`✓ std3`).

*Citation.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

Conjecture 2.1, p. 3: “For each N ∈ ℕ, there is an n ∈ ℕ so that among all n-gons with area 1, ρ_N has no maximizer.” The natural N includes zero. The existential polygon index n represents n + 3 sides; the area is planar volume. Polygon.boundary is the closed path v₀ → v₁ → ⋯ → vₙ₊₂ → v₀ in IsPolygonRegion.

**Theorem 1.2 (result).**

$$\forall N: \mathbb{N}, \exists n: \mathbb{N}, \neg (\exists P: Set\left(\mathbb{C}\right), (IsPolygonRegion\left(n\right)\left(P\right)) \land ((volume\left(P\right) = 1) \land (\forall Q: Set\left(\mathbb{C}\right), (IsPolygonRegion\left(n\right)\left(Q\right)) \Rightarrow ((volume\left(Q\right) = 1) \Rightarrow (rhoN\left(N\right)\left(Q\right) \le rhoN\left(N\right)\left(P\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result` (`✓ std3`). ∎

*Resolves.* `Problems/kraus-simanek-2024-polynomial-content-no-maximizer` (proved) by `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kraus-simanek-2024-polynomial-content-no-maximizer","declaration_gid":"D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

Put m = max(3, N + 2). Alternate long and short radial vertices at angles π/m, choosing the short radius so that the area is one. The resulting 2m-gon is simple. Rotation through 2π/m annihilates the moments of orders 1 through N + 1, so the polynomial content equals the second moment. A positive-area cap has squared norm bounded below by a positive multiple of the squared long radius. Thus the polynomial content is unbounded, and no polygon can maximize it.

## References

- Truth anchor: `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.claim`
- Truth anchor: `D5/S3/Analytic/Torsion/PolynomialContentNoMaximizer.result`
- Dependency: [D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation](PlanarFanPolynomialApproximation.md)
