# Formal Degree

## Abstract

Formal Degree

Orbital integral times denominators is an antisymmetric Laurent polynomial confined by K-types. Orbital integral is Weyl's character minus off-orbit part, which lacks low monomials. Formal degree equals Weyl's dimension polynomial, and (−1)^{pq} times the sum over permutations of elliptic orbital integrals equals p!q! times the conjugate of Weyl's character.

**Theorem 1.1 (harish_chandra_degree_and_orbital).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/FormalDegree.harish_chandra_degree_and_orbital`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/FormalDegree.harish_chandra_degree_and_orbital` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Harish-Chandra: for λ of gap 500n³+10n⁵ and signature (p,q), deg_λ = ∏_{λ_j<λ_i}(λ_i−λ_j)/∏_{i<n} i!; for x in the torus with distinct entries, (−1)^{pq} Σ_{σ∈S_n} ∫_G e_λ(g⁻¹(x∘σ)g) dg = p!q!·conj χ(x), χ the character of U(n) of highest weight λ−ρ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/FormalDegree.harish_chandra_degree_and_orbital`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/SectorBound](SectorBound.md)
