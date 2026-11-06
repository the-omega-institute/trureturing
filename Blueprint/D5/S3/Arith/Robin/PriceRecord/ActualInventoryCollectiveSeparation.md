# Actual integer separation of singleton and collective Robin comparisons

## Abstract

An actual own-clock strict inventory passes every prime singleton test while a fresh finite product improves the original Robin margin.

Set N=2021649740510400=2^6·3^3·5^2·7^2·11·13·17·19·23·29·31 and M=N·37·41·43·47=6198089008491993412800. The price is the original own-clock value 1/(log N·log(log N)). The comparison is the repository's original logarithmic Robin margin, not a changed linear objective.

**Theorem 1.1 (The same integer supplies every original witness clause).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.actual_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.actual_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete OwnClockInventorySingletons bundle preserves N>55440, 55440 dividing N, log N>16, positive own price strictly below the literal boundaryPrice, global golden resource optimality, strict advantage over every different positive integer, both strictInteger and maximalInteger identities, and strict included/excluded inequalities for every prime and positive layer. In particular no prime layer ties the own price.

The same z is the unique first-layer price root on all real t>1. It satisfies z>11, 0<log N−z<1/2, 34<z<35, floorNat(z)=34 and exact inclusive prime support primesLE(floorNat(z)). The same alpha,beta satisfy the literal NonlinearPrimeGap with uniqueness of both nonlinear roots on all x>1, and the stronger strict slacks 31<alpha and beta<37.

For every prime divisor p of N, the actual integer cofactor N/p exceeds 5040 and has strictly larger original margin. For every prime p, Np has strictly larger original margin. At supported primes the proofs use the actual last layer v_p(N) and actual next layer v_p(N)+1; all omitted primes p>=37 are handled by the monotone literal insertion barrier. No original-margin minimum or nonpositive failure premise is present.

The four fresh primes have product 3065857 and exact Euler gain product 3370752/3065857. M has strictly smaller original margin than N, and both original margins are positive. No claim that four is the smallest possible improving prefix is made.

The numeric inequalities reuse RobinRationalBasis.rational_log_bounds, log_expansion_remainder_bound, log_interval_bounds and eulerMascheroni_decimal_bounds. Small finite atanh sums and rational endpoint arithmetic are checked by Lean. External Python intervals motivated the witness and supply no theorem premise or trusted axiom. The original conditional cutoff, root and monotonicity suppliers are exposed in place and consumed without using their failure wrappers.

This is a finite nonimplication result about replacing collective fresh-prime comparisons by the full inventory and singleton bundle. It does not establish RH, a global original Robin minimum, a full integral bound, or separate nonredundancy of every density or geometric-mean consequence. No originality or literature priority claim is made. The mirrored source/readout audit is unfinished: the native producer reports declared_unresolved with source.selection_missing for the closed integer constants. The compiled bridge, variation, sensitivity and observational dependence do not supply the missing source selection. The precise remaining audit obligation is tracked at https://github.com/the-omega-institute/trureturing/issues/27332.

**Theorem 1.2 (The universal finite-product implication is false).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formally negated claim quantifies over the complete own-clock bundle and every finite set of fresh primes. The exact N and the set {37,41,43,47} refute it. The source witness is consumed by this designated utility refutation.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.actual_witness`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualInventoryCollectiveSeparation.result`
- Dependency: [D5/S3/Arith/GoldenResource/RobinRationalBasis](../../GoldenResource/RobinRationalBasis.md)
- Dependency: [D5/S3/Arith/GoldenResource5040PriceInterval](../../GoldenResource5040PriceInterval.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion](NonlinearPrimeExclusion.md)
