# Strengthened Mertens error

## Abstract

The unconditional Mertens logarithmic error is smaller than the inverse square logarithm.

**Theorem 1.1 (Inverse-square logarithmic error).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/Mertens.strengthened_mertens`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/Mertens.strengthened_mertens` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original inclusive Mertens error E3, positive constants c and C give abs(E3(x))<=C exp(-c(log(x))^(1/10)) for all sufficiently large x. Consequently E3(x)=o(1/log(x)^2). The Euler constant and all prime-power endpoints are retained exactly. No Riemann hypothesis or supplied stronger Mertens estimate is assumed.

The existing unconditional weighted Mangoldt rate bounds E1Lambda(x)+gamma by a stretched exponential. Substitution into the exact E2Lambda identity cancels the constant term and bounds both the endpoint and complete integral by the same rate divided by log(x). The exact complete Mangoldt identity expresses E3 as minus E2Lambda minus the omitted prime-power residual. Each residual is bounded by its corresponding omitted lcm Euler logarithm, whose existing total bound is 4/sqrt(x). Both errors vanish after multiplication by log(x)^2.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/Mertens.strengthened_mertens`
- Dependency: [D5/S3/Arith/Robin/LcmRobinResponse](../../LcmRobinResponse.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus](../../PriceRecord/FullPrimePowerArithmeticSurplus.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedMangoldtRate](../../../../Weil/Mertens/WeightedMangoldtRate.md)
