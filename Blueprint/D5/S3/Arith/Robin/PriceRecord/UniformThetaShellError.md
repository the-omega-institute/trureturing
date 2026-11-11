# Exact supremum over the real theta-error shell

## Abstract

Exact supremum over the real theta-error shell.

shellError(X) is the sSup of the exact image {|theta(y)-y| : y is real and X/2<=y<=2X}. The source proves nonemptiness, boundedness using monotonicity and nonnegativity of the existing theta, domination of each actual real shell point, and the supremum upper-bound rule. Existing coarse prime_number_limits supplies one all-real tail for theta(y)/y; a threshold 2Y controls the entire shell and gives shellError(X)/X tending to zero. The source also treats real, including negative, exponents in a global conditional theta law by bounding logarithms of ratios. It never replaces the supremum by a postulated envelope.

**Theorem 1.1 (errorValues nonempty).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem errorValues_nonempty {X : ℝ} (hX : 0 ≤ X) : (errorValues X).Nonempty

**Theorem 1.2 (errorValues bddAbove).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_bddAbove`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_bddAbove` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem errorValues_bddAbove {X : ℝ} (hX : 0 ≤ X) : BddAbove (errorValues X)

**Theorem 1.3 (pointwise le shellError).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.pointwise_le_shellError`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.pointwise_le_shellError` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem pointwise_le_shellError {X y : ℝ} (hX : 0 ≤ X) (hy : y ∈ Set.Icc (X / 2) (2 * X)) : |Chebyshev.theta y - y| ≤ shellError X

**Theorem 1.4 (shellError nonneg).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem shellError_nonneg {X : ℝ} (hX : 0 ≤ X) : 0 ≤ shellError X

**Theorem 1.5 (shellError le).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem shellError_le {X A : ℝ} (hX : 0 ≤ X) (hA : ∀ y : ℝ, y ∈ Set.Icc (X / 2) (2 * X) → |Chebyshev.theta y - y| ≤ A) : shellError X ≤ A

**Theorem 1.6 (shellError eventually le mul).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_eventually_le_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_eventually_le_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem shellError_eventually_le_mul {ε : ℝ} (hε : 0 < ε) : ∀ᶠ X : ℝ in atTop, 0 < X ∧ shellError X ≤ ε * X

**Theorem 1.7 (shellError ratio tendsto zero).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_ratio_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_ratio_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem shellError_ratio_tendsto_zero : Tendsto (fun X : ℝ => shellError X / X) atTop (𝓝 0)

**Theorem 1.8 (shell rpow bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shell_rpow_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shell_rpow_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem shell_rpow_bound {X y : ℝ} (hX : 0 < X) (hy : y ∈ Set.Icc (X / 2) (2 * X)) (a : ℝ) : y ^ a ≤ (2 : ℝ) ^ |a| * X ^ a

**Theorem 1.9 (shellError global power).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_global_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_global_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem shellError_global_power {σ B K Y : ℝ} (hK : 0 ≤ K) (hglobal : ∀ y : ℝ, Y ≤ y → 0 < y → 0 < log y → |Chebyshev.theta y - y| ≤ K * y ^ σ * (log y) ^ B) : ∀ X : ℝ, max 4 (2 * Y) < X → shellError X ≤ (K * (2 : ℝ) ^ |σ| * (2 : ℝ) ^ |B|) * X ^ σ * (log X) ^ B

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_bddAbove`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_nonempty`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.pointwise_le_shellError`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_eventually_le_mul`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_global_power`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_le`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_ratio_tendsto_zero`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shell_rpow_bound`
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
