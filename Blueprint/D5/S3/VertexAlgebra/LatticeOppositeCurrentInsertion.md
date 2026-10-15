# Actual One-Current Opposite Insertion

## Abstract

The actual one-current opposite insertion reverses composition only after the current zero correction is included.

All operators act on the original unrestricted finite-support matter carrier. A denotes an actual neutral current; Y is the original reconstructed state-field. The reflection identity separates the current-zero action from the positive-current tail. The term Y(A(0)b) combines with Y(b)A(0) through the existing actual zero-mode commutator. This is necessary for charged states and does not use an invariant form or a generator-adjoint premise.

**Theorem 1.1 (Supported zero-term separation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.finsum_zero_succ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.finsum_zero_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual finite-support additive sequence, its supported sum is its zero term plus its successor tail. This separates the original current-zero term and shifts the finite first reversed sum.

**Theorem 1.2 (Finite successor decomposition).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.sum_successor_pair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.sum_successor_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If f(0)=a(0) and f(j+1)=a(j+1)+b(j), then the sum through j=N is the sum of a through N plus the sum of b through N-1. This normalizes actual translated and current-inserted Sugawara descendants at a shared finite cutoff.

**Theorem 1.3 (Zero-corrected actual current reflection).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.current_one_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.current_one_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y(A(-1)b)[p]v+Y(A(0)b)[p-1]v is the sum of A(-s)Y(b)[p+s-1]v for s>=0 and Y(b)[p-t-2]A(t+1)v for t>=0. Both orders are supported on the actual tested vector; the s=0 term is the corrected left current-zero action.

**Theorem 1.4 (Actual opposite insertion at frequency one).**

Lean statement: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.opposite_current_one_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.opposite_current_one_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With both inverse-Gram equations, O_(A(-1)b)(n)v equals minus the first reversed sum O_b(n+t)A(t+1)v and minus the second reversed sum A(-s)O_b(n-s-1)v. The common finite descendant cutoff covers b and A(-1)b before any reindexing. The finite union of actual truncation supports permits the sum exchange. This theorem is the frequency-one case; it does not assert the general frequency-r opposite insertion or any descendant BPZ or Hermitian adjoint law.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.current_one_reflection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.finsum_zero_succ`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.opposite_current_one_insertion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeOppositeCurrentInsertion.sum_successor_pair`
- Dependency: [D5/S3/VertexAlgebra/LatticeOppositeCoefficients](LatticeOppositeCoefficients.md)
