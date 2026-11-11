# Exact sharp scalar reduction and two Young bounds

## Abstract

Exact sharp scalar reduction and two Young bounds.

Assume the stated finite budget, V<=T, W<=Delta+delta, delta<=2log X, the logarithm comparison, and the coercivity estimate for Delta. Then R<=a T sqrt(R)/X^(5/4)+a(T/X)R+dTlog X/X^2+2/X, with a=12000 and d=24000. Absorption uses T=E+5sqrt X and the hypothesis aT/X<=1/4. The square (sqrt R/2-aT/X^(5/4))^2 absorbs the square-root term. A second Young square absorbs Tlog X/X^2. The bound log^2 X<=sqrt X is the hlog hypothesis of scalar_absorption; it can be supplied eventually by an upstream logarithmic little-o result and is not proved by this declaration. q=2a^2+d and finalConstant=52q+d+4 give the exact E^2/X^(5/2)+1/X rate.

**Theorem 1.1 (scalar budget reduction).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_budget_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_budget_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem scalar_budget_reduction {X T V W Δ δ R : ℝ} (hX : exp 2 ≤ X) (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W) (hVT : V ≤ T) (hWΔ : W ≤ Δ + δ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2 * log X) (hhalf : log X / 2 ≤ log (X / 2)) (hR : R ≤ 6 * V * W / (X ^ 2 * log (X / 2)) + δ / (X * log X)) (hΔ : Δ ≤ 1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2)) : R ≤ a * T / X ^ (5 / 4 : ℝ) * sqrt R + a * (T / X) * R + d * T * log X / X ^ 2 + 2 / X

**Theorem 1.2 (scalar absorption).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_absorption`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem scalar_absorption {X E R : ℝ} (hX : 1 < X) (hE : 0 ≤ E) (hR0 : 0 ≤ R) (hsmall : a * ((E + 5 * sqrt X) / X) ≤ 1 / 4) (hlog : log X ^ 2 ≤ sqrt X) (hR : R ≤ a * (E + 5 * sqrt X) / X ^ (5 / 4 : ℝ) * sqrt R + a * ((E + 5 * sqrt X) / X) * R + d * (E + 5 * sqrt X) * log X / X ^ 2 + 2 / X) : R ≤ finalConstant * (E ^ 2 / X ^ (5 / 2 : ℝ) + 1 / X)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_absorption`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_budget_reduction`
