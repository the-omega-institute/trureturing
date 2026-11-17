# Cell quadrature

## Abstract

Bounded variation quadrature for integer floor sampling.

**Theorem 1.1 (Integrability of a floor step function).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.floor_step_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.floor_step_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real sequence F and finite real endpoints a and b with a>=0, the function F(floor x) is interval integrable from a to b. Only finitely many natural floor values occur between the endpoints.

**Theorem 1.2 (Floor step integral).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.floor_step_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.floor_step_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural a and real y>=a, the integral of F(floor x) from a to y is the sum of F(n) over a<=n<floor y plus (y-floor y) F(floor y).

**Theorem 1.3 (Weighted quadrature with endpoint cells).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.cell_quadrature`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.cell_quadrature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be at least two and A be nonnegative. Suppose the absolute value of F(n) is at most A for integers from floor(N) through ceil(2N). Let w vanish outside [1,2], with its supremum bound plus total variation at most B. The integral of w(x/N) F(floor(x)) over [N,2N] differs from the sum of w(n/N) F(n) over N<n<=2N by at most 3 A B. Fractional endpoint cells and the shift between left cells and right endpoint sums are included, and values of w at integer sample points are retained.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.cell_quadrature`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.floor_step_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature.floor_step_intervalIntegrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation](BVCorrelationSummation.md)
