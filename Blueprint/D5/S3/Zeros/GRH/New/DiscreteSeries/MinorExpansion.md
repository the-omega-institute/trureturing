# Minor Expansion

## Abstract

Minor Expansion

Second-order expansion of log principal minors near 1 with absolute error constants.

**Theorem 1.1 (exists_principalMinor_eq_exp).**

Lean statement: `D5/S3/Zeros/GRH/New/DiscreteSeries/MinorExpansion.exists_principalMinor_eq_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/DiscreteSeries/MinorExpansion.exists_principalMinor_eq_exp` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let λ have gap h, X = g−1, ‖X‖ < 10⁻³ (Frobenius). Some y has ψ_λ(g) = HCParam.flenstedJensen(1,y) and, for k∈K and projectors P to sets p of lowest entries of λ, Δ_p(k*yk) = exp(tr(P log g)+‖[P,X]‖²/4+r), |r| ≤ 2·10⁵‖X‖(‖[P,X]‖²+‖[P,k]‖²).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/DiscreteSeries/MinorExpansion.exists_principalMinor_eq_exp`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/FramedCoefficient](../../Lib/General/LinearAlgebra/FramedCoefficient.md)
