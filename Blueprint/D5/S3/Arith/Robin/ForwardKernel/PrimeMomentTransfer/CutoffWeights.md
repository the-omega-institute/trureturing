# Cutoff weights

## Abstract

Closed interval cutoffs give bounded variation weights for dyadic moments.

**Theorem 1.1 (Indicator cutoff bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.cutoff_bv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.cutoff_bv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= u <= v <= 2, the indicator of the closed interval [u,v] vanishes outside [1,2], has supremum at most one, and has total variation at most two. Its supremum bound plus total variation is at most three, also when u=v.

**Theorem 1.2 (Logarithmic block weight bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.log_block_bv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.log_block_bv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= u <= v <= 2, extend 1/(t log 2) by zero outside the closed interval [u,v]. The resulting function vanishes outside [1,2], has supremum at most 1/log 2 and total variation at most 2/log 2. Their sum is at most 3/log 2, including a single-point interval.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.cutoff_bv`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.log_block_bv`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
