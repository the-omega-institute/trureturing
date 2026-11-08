# The first continuum cell

## Abstract

The original strict half-surplus on the first continuum cell, retaining the actual integer and every prime-power tail.

**Theorem 1.1 (All actual integers on 11 < z <= 13).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HalfSurplusFirstCell.original_half_surplus_first_cell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HalfSurplusFirstCell.original_half_surplus_first_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real 11<z<=13 and every positive integer n with primeFactors(n)=primesLE(floor(z)) and 0<log(n)-z<1/2, let A=tail(n)+(log(n)-psi(z))/(z*log(z))-fullPrimePowerResidual(z), and K=log(log(z))+(log(n)-z)/(z*log(z))-log(log(log(n))). Then sqrt(z)*log(z)*(A-K)>1/2. The full original support, every actual exponent, the signed inventory and the exact curvature are part of the statement. This is the first continuum cell toward the unchanged all-z>11 target; it asserts nothing for z>13 and no RH or global Robin-5040 conclusion.

Write lambda=1/(z*log(z)), a_p=v_p(n), b_p=floor(log(z)/log(p)), and r_p for the entire omitted prime-power tail. FullPrimePowerArithmeticSurplus.full_surplus_eq_sum identifies A with the sum of c_p=layerTail(n,p)+(a_p-b_p)*lambda*log(p)-r_p. Its prime_contribution_pos makes every contribution positive on the literal support, including underfilled inventories. These established suppliers retain summability, all omitted powers and equality at p^k=z; those arguments are reused.

On this cell b_2=3, b_3=2 and b_5=1. The actual prices satisfy 1/52<lambda*log(2)<7/253, 3/104<lambda*log(3)<12/253 and lambda*log(5)>1/26. The exact boundary losses are log(31/30), log(63/62), log(13/12) and log(40/39). Bounds 1-1/x<=log(x)<x-1 give the required strict price separations. GoldenLocalThreshold.golden_prime_local_objective_maximal_of_threshold, using the established strict decrease of the golden layer marginal, compares all natural exponents at once. Its application gives scalar minima at 4, 2 and 1 for the three contribution directions. The comparison acts on the actual a_2,a_3,a_5 and does not replace n or claim a minimizer of the original integer domain.

The complete prefix/residual supplier gives r_2=log(2)-2/3, r_3=log(3/2)-7/18 and r_5=log(5/4)-1/5. Thus A>=C+lambda*log(2), where C=113/90+log(120/403). The existing RobinRationalBasis atanh remainder at q=283/523 and three terms bounds log(403/120) by 2*(q+q^3/3+q^5/5)+2*q^7/(7*(1-q^2)). Exact rational arithmetic yields C>=3470774833217983807/79477468742214794160>21/500. The certified logarithm brackets used for 2,3,5,11,13 come from ActualInventorySmallPrimeBounds; no decimal evaluation serves as proof.

The public CurvatureCorrectedArithmeticSurplus supplier gives 0<K<(log(z)+1)/(8*z^2*log(z)^2) at the original M=log(n)-z. With s=sqrt(z), L=log(z), one has s>33/10, L>239/100, log(2)>69/100 and s<181/50. Hence s*L*A>(33/10)*(239/100)*(21/500)+69/362 and s*L*K<5/968. Their difference is 1/2+182834427/10950500000, so the target is strict. The open endpoint eleven and closed endpoint thirteen are both preserved; the new thirteen contribution is positive and is included in the sum before discarding it.

Attribution: this is the supplied first-cell mathematical argument, implemented using the named canonical surplus, scalar objective, rational logarithm and curvature suppliers. The scalar threshold method and atanh remainder are classical; no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HalfSurplusFirstCell.original_half_surplus_first_cell`
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](../../GoldenLocalThreshold.md)
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualInventorySmallPrimeBounds](ActualInventorySmallPrimeBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus](CurvatureCorrectedArithmeticSurplus.md)
