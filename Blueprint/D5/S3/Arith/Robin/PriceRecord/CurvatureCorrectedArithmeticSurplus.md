# Arithmetic surplus after curvature

## Abstract

The full prime-power arithmetic surplus pays the literal log-log curvature loss.

**Theorem 1.1 (The quantitative root-scale remainder).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_sub_curvature_root_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_sub_curvature_root_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z>11, 0<M<1/2 and every positive integer n on the exact initial prime support, the full signed surplus minus K exceeds 1/(4000*sqrt(z)*log(z)), where K=log(log(z))+M/(z*log(z))-log(log(z+M)). The existing curvature bound and old arithmetic estimate prove K<Delta/2. The all-z root-scale theorem supplies Delta>1/(2000*sqrt(z)*log(z)); thus half of the actual surplus remains. No exponent, containment, signed-integral or extremality premise is added.

**Theorem 1.2 (A strict positive remainder for the actual finite state).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_dominates_loglog_curvature`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_dominates_loglog_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z>11, 0<M<1/2, and an actual positive integer n with exactly the prime support p<=z, with no assumption that n contains all prime powers up to z, let K=log(log(z))+M/(z*log(z))-log(log(z+M)). Then 0<K<(log(z)+1)/(8*z^2*log(z)^2), and the full arithmetic surplus minus K exceeds log(2)/(12*z*log(z)). The surplus uses the literal tail(n), log(n)-Chebyshev.psi(z), and all omitted prime-power layers k>=2; prime-power equality remains in psi.

The private curvature estimate uses two applications of log(1+u)>=u-u^2/2, obtained from the existing rational lower bound 2*u/(u+2)<=log(1+u). Existing strict log-log tangency gives K>0. The stronger actual full_prime_power_arithmetic_surplus theorem supplies the arithmetic lower bound for arbitrary positive valuations on this exact support, including underfilled prime-power inventories. Its signed deficit argument retains the entire reference tail; no hcontains premise is used. This finite-state inequality assumes neither a desired residual sign nor a signed-integral identity, and asserts no RH conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_dominates_loglog_curvature`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_sub_curvature_root_scale`
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](../LogarithmBounds.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullPrimePowerArithmeticSurplus](FullPrimePowerArithmeticSurplus.md)
