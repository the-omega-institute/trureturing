# Homogeneous Coords

## Abstract

Homogeneous Coords

Homogeneous Noether normalisation and Galois closure of the cone over a variety. Homogeneous coordinates of points under a projective embedding; global functions constant on components.

**Theorem 1.1 (exists_galois_closure).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/HomogeneousCoords.exists_galois_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/HomogeneousCoords.exists_galois_closure` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Galois closure: a Noether normalisation Λ of g yields a finite group G, finite injective f: k[X] → B and solutions b_σ of the homogeneous equations of g with Λ(b_σ) = f(X), such that geometric points φ, ψ with ψf(X) = uφf(X) have ψ(b_σ) = uφ(b_{τσ}) for some τ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/HomogeneousCoords.exists_galois_closure`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Geometry/ProperAtlas](../../General/Geometry/ProperAtlas.md)
