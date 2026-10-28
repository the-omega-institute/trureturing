# Strict Euler Inventory Root Correction

## Abstract

The strict Euler inventory has uniform root correction sqrt(2)-1.

For every positive epsilon, one real threshold T>1 works for every real t>=T and every positive natural U satisfying the literal strict prime factorization law, with |(log U-psi(t))/sqrt(t)-(sqrt(2)-1)|<epsilon. Equality layers remain excluded.

**Theorem 1.1 (Finite envelope for the complete third-and-higher layer mass).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t>=2 and every positive natural U satisfying the literal strict factorization law, the sum of (factorization(q)-2)*log(q) over prime factors with factorization(q)>=3 is at most ((3*t)^(1/3)+1)*log(t*log(t)/log(2)). The proof uses the actual active-power cutoff and a finite support count; all active exponent layers remain in the mass.

**Theorem 1.2 (Uniform root-scale vanishing of layers at least three).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_vanishing`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon there is one threshold T>1 such that every real t>=T and every positive strict inventory integer U have third-and-higher layer mass divided by sqrt(t) below epsilon. An explicit 240*t^(-7/60) envelope proves the uniform limit.

**Theorem 1.3 (Uniform second-layer mass coefficient).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_second_layer_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_second_layer_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal sum of log(q) over prime factors with exponent at least two, divided by sqrt(t), tends uniformly to sqrt(2). For every 0<c<sqrt(2), all primes q<=c*sqrt(t) are strictly active beyond one common threshold: the logarithmic marginal is bounded below using 1/(q^2+q+1). Actual active squares satisfy q^2<2*t. Unconditional PNT squeezes the weighted mass between the two theta functions. Equality events are included in t and excluded from the active layers.

**Definition 1.4 (Exact root-scale statement).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction_statement`

*Formalization.* `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction_statement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The statement keeps all real parameters, all prime factorization equalities and all positive natural inventory integers. The following theorem proves this exact proposition.

**Theorem 1.5 (Uniform strict inventory root correction).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof splits log(U) into first, second and all remaining layers. The first-layer error is bounded by log(t), the second layer contributes sqrt(2)*sqrt(t), and the entire higher tail is o(sqrt(t)). Costa-Pereira bounds and the existing unconditional MediumPNT give (psi(t)-theta(t))/sqrt(t)->1. Combining the four errors gives the exact uniform coefficient sqrt(2)-1. This is an arithmetic supplier for the Robin/5040 program, and does not prove RH or a signed-tail or attainment statement.

The paper and theory attribution is the existing ZECKENDORF_EULER_5040 Definition 7.1, Theorem 8.1 and equations (19)--(24), as cross-referenced by the existing analytic workload note. The existing Lean O(sqrt(t)) bound is not presented as this exact asymptotic. The outer Reg source binding remains unfinished and does not claim a validated four-slot registration.

## References

- Truth anchor: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction`
- Truth anchor: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction_statement`
- Truth anchor: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_second_layer_limit`
- Truth anchor: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_bound`
- Truth anchor: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_vanishing`
- Dependency: [D5/S3/Arith/Robin/EulerLayerInventoryGrowth](EulerLayerInventoryGrowth.md)
