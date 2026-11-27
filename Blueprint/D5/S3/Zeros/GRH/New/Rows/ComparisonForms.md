# Comparison Forms

## Abstract

Comparison Forms

Integral comparison forms seeing the twist through one number. There are forms on a definite unitary group, integral off the twist's conductor, short when untwisted and orthogonal as the congruence bound requires, whose descents to U(W_j) detect all good forms and see the twist only through one number made of Hecke L-values, and they cancel a lift's unknown volume. Integral forms pairing with a lift to an explicit L-value (pullback, seesaw) are known in low rank. Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; Y.-S. Lee, Hida family of theta lift from U(1) to definite U(2), 2024; Prasanna, Integrality of a ratio of Petersson norms, 2006.

**Theorem 1.1 (exists_comparison_forms).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/ComparisonForms.exists_comparison_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/ComparisonForms.exists_comparison_forms` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Comparison forms: there are γ_ϑ ≠ 0 with |γ_ϑ/γ_1|² = Γ(ϑ)/Γ(1) (Data.heckeValueProd), a linear surjection A from tables onto good forms on U(W_j), and linear Ξ_ϑ with u_ϑ*Ξ_ϑ = γ_ϑA (Data.goodLift), Ξ_ϑA*y tested, Ξ_ϑζ φ-integral for l prime to ϑ.levelNorm and ζ̄ integral at φ∘conj, and 𝗁‖Ξ_1ζ‖²_σ ≤ exp(2rB₀)∑_a‖σζ_a‖² (𝗁 = smallHookNumber).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/ComparisonForms.exists_comparison_forms`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/FillingTheorem](../Filling/FillingTheorem.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/CartanIntegrality](CartanIntegrality.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/RowVolume](RowVolume.md)
