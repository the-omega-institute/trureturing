# Canonical Robin margins on a prescribed mesh

## Abstract

Two-sided Robin oscillation on prescribed meshes with power-saving gaps

Write Θ for zeroAbscissa, the supremum of the real parts of the nontrivial Riemann zeta zeros. For a natural j, let R(j) = robinLogMargin(strictInteger(firstLayerPrice(j+1))), with j cast to ℝ in the price. Fix a strictly increasing N from ℕ to ℕ, and suppose eventually N(k+1) − N(k) ≤ G N(k)^(1−eta) for real G ≥ 0 and eta > 0. Put d = min(eta, 1/2) and take 1 − Θ < alpha ≤ 1/2.

**Theorem 1.1 (A uniform canonical margin bound below an actual zero exponent).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh.exists_canonical_robin_margin_cell_bound_below_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh.exists_canonical_robin_margin_cell_bound_below_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are real a, epsilon and K with 0 < a < alpha, epsilon > 0 and K > 0, and an actual nontrivial zero ρ with Θ + epsilon − d < 1 − a < Re(ρ). For every sufficiently large k and every natural j in the closed cell N(k) ≤ j ≤ N(k+1), writing X = N(k), one has |X^a log(X) (R(j) − R(N(k)))| ≤ K X^(a + Θ + epsilon − 1 − d) log(X).

The canonical cutoff at j lies in [j+1, j+3/2] and its price equals firstLayerPrice(j+1) exactly. The gap bound implies N(k+1)/N(k) → 1, so late cell cutoffs lie between X and 4X. The clock is at least X/2 by uniform inventory growth and differs from its cutoff by at most a constant times X^(Θ + epsilon) by the Chebyshev estimate.

RobinMarginModulus.canonical_robin_margin_cell_bound bounds the absolute margin increment by the clock increment times a constant times X^(Θ + epsilon − 2)/log(X). The cell width and the two square-root endpoint errors bound the clock increment by a constant times X^(1−d) log(X). Multiplying these bounds and the weight X^a log(X) gives the displayed power.

Choose epsilon = min(alpha − (1 − Θ), d)/4 and a = 1 − Θ + epsilon. This gives Θ + epsilon − d < 1 − a < Θ. The defining supremum then supplies an actual nontrivial zero with Re(ρ) > 1 − a.

**Theorem 1.2 (Opposite infinite limits on subsequences of the prescribed mesh).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh.actual_canonical_two_signed_subsequences_of_power_saving_gaps`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh.actual_canonical_two_signed_subsequences_of_power_saving_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume in addition that Re(z) < Θ for every nontrivial zeta zero z. There are strictly increasing mesh index sequences qpos and qneg. With x = N(qpos(k)), the quantity x^alpha log(x) R(x) tends to +∞, and with x = N(qneg(k)) it tends to −∞. The range includes alpha = 1/2.

The chosen zero gives 1 − Θ < a, and a < alpha ≤ 1/2. Apply RobinVanishingRelativeGap.actual_canonical_two_signed_ratio_one_meshes at a to obtain the two signed witness sequences. The uniform cell error at this weight tends to zero since its power exponent is negative, so it is eventually at most one. Use PolynomialMeshBounds.mesh_bracket_of_strictMono to put each late witness j in the cell X = N(k) ≤ j < N(k+1). Since j ≤ 2X eventually, PolynomialMeshBounds.record_weight bounds j^a log(j) by 4 times X^a log(X).

The weight comparison preserves divergence of positive witnesses when weighted at X, and the bounded cell error transfers that divergence to R(X). Apply the same argument to the negated margin for the negative witnesses. The cell indices tend to infinity, so each sequence admits strictly increasing mesh indices. On either subsequence the exact factor X^(alpha−a) tends to +∞ and changes the weight from a to alpha while preserving the signed limit.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh.actual_canonical_two_signed_subsequences_of_power_saving_gaps`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh.exists_canonical_robin_margin_cell_bound_below_zero`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PolynomialCanonicalRecordCriterion](PolynomialCanonicalRecordCriterion.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds](PolynomialMeshBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RobinMarginModulus](RobinMarginModulus.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap](RobinVanishingRelativeGap.md)
