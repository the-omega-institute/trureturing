# Component Bound

## Abstract

Component Bound

Kolyvagin derivative cocycles of Gauss sums: ramification and the Frobenius-to-inertia relation. Artin reciprocity and Kummer duality relations for twisted cocycles over cyclotomic fields. Stickelberger annihilation of odd twisted classes; Kolyvagin-Rubin bound on detecting elements.

**Theorem 1.1 (exists_detecting_points_component).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/ComponentBound.exists_detecting_points_component`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/ComponentBound.exists_detecting_points_component` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Kolyvagin–Rubin bound. Under the hypotheses of nsmul_component_eq_zero (these already make O local and each O/lⁿ finite), with X ≠ 0 and l > N + e + 3, there are v_l(X) + 1 Galois elements such that a cocycle in component vanishing at all of them is zero.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/ComponentBound.exists_detecting_points_component`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/TameCocycles](../../ClassField/GaloisCohomology/TameCocycles.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/RegularityFrobenius](../../PadicHodge/Crystalline/RegularityFrobenius.md)
