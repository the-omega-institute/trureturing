# Finite Density Marginal Calculus

## Abstract

Actual tensor-coordinate partial traces compose and respect basis relabeling.

Every state is the existing project DensityState. reduceState e rho keeps K and sums the actual matrix diagonal over R, where e identifies K tensor R with the original carrier. The coordinate equivalence is explicit; no entropy values or marginal consistency assumptions are supplied.

**Theorem 1.1 (Two actual traces compose).**

$$\operatorname{reduce}\left(f, \operatorname{reduce}\left(e, \rho\right)\right) = \operatorname{reduce}\left(\operatorname{compose}\left(e, f\right), \rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MarginalCalculus.reduceState_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracing R and then T equals tracing T tensor R, after the actual tensor associator. The proof is the finite product-sum identity on matrix entries.

**Theorem 1.2 (SSA after a tensor partition).**

$$\operatorname{S}\left(KSR\right) + \operatorname{S}\left(S\right) \le \operatorname{S}\left(KS\right) + \operatorname{S}\left(SR\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/MarginalCalculus.ssa_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual density state and any equivalence to K tensor S tensor R, the receiving SSA theorem applies to the three real marginals. A coordinate sum proves that the retained central register is exactly the iterated partial trace.

## References

- Truth anchor: `D5/S3/Quantum/Information/MarginalCalculus.reduceState_compose`
- Truth anchor: `D5/S3/Quantum/Information/MarginalCalculus.ssa_partition`
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity](StrongSubadditivity.md)
