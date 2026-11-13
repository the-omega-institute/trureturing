# Actual dyadic root stencil

## Abstract

Actual dyadic root stencil.

**Theorem 1.1 (Transfer to the actual clamped root).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.uniform_boundary_root_log_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.uniform_boundary_root_log_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both independent BHP suppliers and for each fixed j>=2, positive A,T precede every full record and original mu>0. The difference between j*log(layerPrime(m,j)) and log(P)+actualOffset(j,P) is at most A*P^(-19/(40*j)). The actual clamped cutoff and the occupied boundary remain distinct objects.

**Theorem 1.2 (Four dyadic mesh limits).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_stencil_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_stencil_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At infinity the four actual dyadic mesh limits are respectively log(2), log(2)^2, 2*log(2)^3 and 6*log(2)^4 after multiplication by log(X), log(X)^2, log(X)^3 and log(X)^4. The first expression is log(X)*(log(2)-mesh1(X)); the remaining expressions use mesh2, mesh3 and mesh4 directly.

**Theorem 1.3 (One signed vector on the actual roots).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_root_greedy_stencil`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_root_greedy_stencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are positive B,T such that every real X>=T admits an integer vector on Fin 5 with sum zero and every coefficient at most B*log(X) in absolute value. The positive fourth mesh is at most B/log(X)^4; the deficit log(2)-sum(v(k)*rootMasses(X,k)) lies in [2*mesh4(X),3*mesh4(X)). These are simultaneous bounds for the same vector.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_root_greedy_stencil`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_stencil_limits`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.uniform_boundary_root_log_transfer`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualBoundaryPriceLocalization](ActualBoundaryPriceLocalization.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualMixedCutoffFourthOrder](ActualMixedCutoffFourthOrder.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder](FullArithmeticCorrectionSecondOrder.md)
