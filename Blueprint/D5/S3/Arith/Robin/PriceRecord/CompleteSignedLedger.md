# The complete signed Robin ledger

## Abstract

The exact full signed ledger at the same integer and cutoff.

**Theorem 1.1 (The full quantitative necessary bound from original failure).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.failure_has_negative_complete_weighted_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.failure_has_negative_complete_weighted_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the SOLE hypothesis that some integer m>5040 has robinLogMargin(m)<=0, including equality failures, the theorem retains the SAME attained global-minimum N>55440 and real cutoff z>11. It preserves the global minimum property; positive own price below boundaryPrice; resource optimality and the strict objective comparison against every other positive integer; strictInteger and maximalInteger identities; absence of all prime-layer ties; positive half-shift log(N)-z<1/2; the exact first-layer root equation and uniqueness on t>1; exact initial prime support; and the unique nonlinear deletion/insertion roots and their entire open prime-gap property. At these same N,z the literal full WeightedTailTransport.weightedTail(CompleteMertensPeak.psiErrorKernel,z) is strictly less than -1/(4000*sqrt(z)*log(z)). The proof consumes the exact signed margin identity and the all-z finite root-scale surplus after K<Delta/2. It adds no hLay, integrability, support, exponent, cofactor, eventual threshold or desired sign hypothesis. It proves a necessary negative bound from original failure; the opposite full-tail lower bound and RH remain open.

**Theorem 1.2 (The literal Robin margin identity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.robin_margin_eq_complete_signed_ledger`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.robin_margin_eq_complete_signed_ledger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real z>=4 and positive integer N with exactly the prime support p<=z, let M=log(N)-z and K=log(log(z))+M/(z*log(z))-log(log(z+M)). Then robinLogMargin(N)=WeightedTailTransport.weightedTail(CompleteMertensPeak.psiErrorKernel,z)+Delta_z(N)-K. Delta is the original Euler tail plus signed log(N)-psi(z) inventory minus the complete strict prime-power residual. The proof consumes the exact Mangoldt/Euler residual equality, the unconditional complete Mertens ledger, and the same-integer finite Euler identity. It adds no hLay, integrability, exponent, or residual-sign hypothesis, defines no substitute integral, and claims no opposite tail lower bound or RH conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.failure_has_negative_complete_weighted_tail`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger.robin_margin_eq_complete_signed_ledger`
- Dependency: [D5/S3/Arith/Robin/CompleteMertensPeak](../CompleteMertensPeak.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus](CurvatureCorrectedArithmeticSurplus.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus](FullPrimePowerArithmeticSurplus.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion](NonlinearPrimeExclusion.md)
