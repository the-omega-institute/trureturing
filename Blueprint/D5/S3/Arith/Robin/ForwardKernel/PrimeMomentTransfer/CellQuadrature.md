# Cell quadrature

## Abstract

Bounded variation quadrature for integer floor sampling.

**Theorem 1.1 (Weighted quadrature with endpoint cells).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.cell_quadrature`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.cell_quadrature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be at least two and A be nonnegative. Suppose the absolute value of F(n) is at most A for integers from floor(N) through ceil(2N). Let w vanish outside [1,2], with its supremum bound plus total variation at most B. The integral of w(x/N) F(floor(x)) over [N,2N] differs from the sum of w(n/N) F(n) over N<n<=2N by at most 3 A B. Fractional endpoint cells and the shift between left cells and right endpoint sums are included, and values of w at integer sample points are retained.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.cell_quadrature`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation](BVCorrelationSummation.md)
