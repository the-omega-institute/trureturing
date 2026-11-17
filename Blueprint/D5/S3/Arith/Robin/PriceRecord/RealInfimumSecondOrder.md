# Complete real-image domain

## Abstract

Exact sixteen for the original prime-prefix real image infimum.

The original complete real-image target uses realInfimum=sInf(realValues), with every supported real exponent at least one and every off-support coordinate unrestricted. It adds no attainment, desired-limit, RH or distribution premise.

**Theorem 1.1 (Actual infimum calibration error at the extra ell scale).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder.actual_calibration_error_negligible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder.actual_calibration_error_negligible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unchanged public error expression is ell*(sqrt(H)*ell*sqrt(ell))*(Q-(realInfimum-baseline)). Set r=1/sqrt(H), u=ell*(exp(r)-1) and A=exp(u)-1. The original RealInfimumPrimeBoundary.real_infimum_fixed_price_squeeze bounds the literal infimum of the same full admissible image by min(r,Q-A^2/ell)<=realInfimum-baseline<=Q. Its source proves the bound on every original feasible vector before applying le_csInf. The finite prime support, cardinality, H>1 and ell>=1 conditions hold eventually by the existing prime-domain suppliers. No attained optimizer, response shift, fixed point, stationarity or new finite-bound hypothesis is used.

The unchanged calibrated_normalization is moved before this theorem. Multiplying its limit by 1/ell and paying log(ell)/ell->0 gives M_Q=sqrt(H)*ell*sqrt(ell)*Q->8. Multiplying by 1/ell and 1/sqrt(ell) gives sqrt(H)*Q->0. Thus eventually Q<=r, and A^2/ell>=0 selects the second branch of the finite minimum. Consequently the full signed error Delta=Q-(realInfimum-baseline) satisfies 0<=Delta<=A^2/ell.

Both exponential remainders are explicit. The pinned logarithm-power limit gives ell*r->0, while r->0 and eventual r>0 give (exp(r)-1)/r->1. Their product proves u->0. Eventual ell>0 and exp(r)-1>0 prove u>0, so the second divided difference (exp(u)-1)/u->1 is valid on a punctured neighborhood. Multiplication and exact cancellation yield A/(ell*r)->1. The consumed generic exp_difference_quotient helper uses the derivative of exp at zero and the paid punctured neighborhood for each of the two arguments.

The upper error has the exact identity ell*(sqrt(H)*ell*sqrt(ell))*A^2/ell = (A/(ell*r))^2*(ell^3*sqrt(ell)/sqrt(H)). For eventual ell>=1, sqrt(ell)<=ell bounds the last factor between zero and ell^4/sqrt(H). The pinned isLittleO_log_rpow_rpow_atTop with powers four and one-half sends this upper bound to zero. The final squeeze retains both sides and the original extra ell scale; no exponential remainder or logarithmic factor is discarded.

**Theorem 1.2 (The exact requested unconditional telescope).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder.actual_real_infimum_second_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder.actual_real_infimum_second_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural P, let H=theta(primesLE P), ell=log H and M=sqrt(H)*ell*sqrt(ell)*(realInfimum(primesLE P)-baseline(primesLE P)). The final source statement remains Tendsto (fun P => ell*(M-8)+8*log ell) atTop (nhds 16), with no theorem premise or section parameter. Small prefixes remain in its domain; positivity is paid only eventually. The final assembly subtracts the direct error limit from calibrated_normalization.

The calibrated_normalization consumes PrimeBoundarySecondOrder.calibrated_Q_second_order and retains C=1+H*ell, Y^2=C, 2*log(Y)=ell+log(ell)+log(C/(H*ell)), and the exact square-root correction. The inherited prime calculation retains both finite tail endpoints Y and P and the actual MediumPNT exponent one-tenth. No RH, PNT, minimizer, calibration-rate or target-limit premise is added.

The direct sublevel proof and scale conversion consume RealInfimumPrimeBoundary, QuantitativePrimeAbel and the frozen PrimeSquareTail theorem. They use neither a global25 package nor minimizer, own-clock contraction or sharp-eight branches.

Every supplier is used by the complete second-order telescope; no separate finite-tail replacement theorem is introduced. The original objective and frozen library declarations retain their defining expressions.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder.actual_calibration_error_negligible`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder.actual_real_infimum_second_order`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder](PrimeBoundarySecondOrder.md)
