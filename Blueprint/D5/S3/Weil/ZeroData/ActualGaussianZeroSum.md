# Absolute convergence of the complete shifted zero sum

## Abstract

Absolute convergence of the complete shifted zero sum.

**Theorem 1.1 (Absolute convergence of the complete shifted zero sum).**

Lean statement: `D5/S3/Weil/ZeroData/ActualGaussianZeroSum.E_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualGaussianZeroSum.E_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occurrence type is the sigma type of every actual zero index and its finite analytic-multiplicity fiber. The existing actual_sigma_inverse_square_summable is transported through actualOccurrenceEquiv, without removing repeated values or either sign of the ordinate. The actual inverse-square mass bound and firstLiMass_lt_one give total mass less than two.

The existing actual_height_gt_ten supplies occurrence_height. Both norm(rho) and norm(1-rho) are at least abs(im(rho)), so the reciprocal coefficient norm is at most im(rho)^(-2). The existing actualH_bound, with its unchanged Li mass, gives norm(H(y))<=2*exp(max(y,0)); its real part satisfies the same absolute bound.

ActualGaussianZeroSum, ActualGaussianLocalWindow, ActualGaussianDirectTail, ActualGaussianEnvelopeMassBudget and OriginalGaussianIntegralBudgets actually consume these estimates. They are source adapters and quantitative consequences of existing suppliers; no independent admission or newly proved actual-zero mass theorem is claimed.

The only proposed shared-supplier change exposes the existing firstLiMass_lt_one and actual_sigma_inverse_square_summable declarations. Their proof bodies are unchanged. This avoids duplicating inaccessible private mathematics.

E(m,gamma) is the sum over all actual occurrences of exp(m*((rho-i*gamma)^2+16*(rho-i*gamma))). No reciprocal weights occur in E itself. For m>=1 and any nonzero real eta, exp(-m*(eta-gamma)^2)<=(2+2*gamma^2)/eta^2. This follows by multiplying the elementary exponential bound by its inverse and using eta^2<=2*(eta-gamma)^2+2*gamma^2.

The actual strip 0<Re(rho)<1 contributes at most exp(17*m). Hence the summand norm is bounded by exp(17*m)*(2+2*gamma^2)*im(rho)^(-2). The actual inverse-square summability pays absolute convergence before the local/complement decomposition. This statement is consumed by ActualGaussianDirectTail.E_eq_local_add_omitted.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualGaussianZeroSum.E_summable`
- Dependency: [D5/S3/Arith/Robin/CompleteActualSignedGaussianExchange](../../Arith/Robin/CompleteActualSignedGaussianExchange.md)
