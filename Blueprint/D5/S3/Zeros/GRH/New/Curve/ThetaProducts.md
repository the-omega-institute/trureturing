# Theta Products

## Abstract

Theta Products

Theta products along tight frames: integral up to one exponential coupling partner places.

**Theorem 1.1 (thetaProducts_normal_form).**

Lean statement: `D5/S3/Zeros/GRH/New/Curve/ThetaProducts.thetaProducts_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Curve/ThetaProducts.thetaProducts_normal_form` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For (p/d) ≠ 1, some ϖ, π with |ϖ| = p^{−ρ_p} (ρ_p = nonsplitWeight), |π| = p^{((p/d)−1)/2} serve all r ≤ 1 and Θ in Parameters.thetaProducts (δ = 1): IsIntegralOnNullCone holds for each B, with couplings j ≤ log_p B, j odd or p = d. If (p/d) = −1 and r = 1, Θ(ϖz) = exp(κΨ)V with |κ| = p^{1−1/(p−1)}, Ψ, V integral, Ψ(0) = 0, and ∂_xΨ has unit coefficients exactly at the z_y^{p^j}, j odd, −p^j y = x.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Curve/ThetaProducts.thetaProducts_normal_form`
- Dependency: [D5/S3/Zeros/GRH/New/Curve/FormalParameter](FormalParameter.md)
- Dependency: [D5/S3/Zeros/GRH/New/Curve/PeriodDefs](PeriodDefs.md)
