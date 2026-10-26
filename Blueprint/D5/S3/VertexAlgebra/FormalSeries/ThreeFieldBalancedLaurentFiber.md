# The numerator index

## Abstract

The numerator index

**Definition 1.1 (The numerator index).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedInput`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three natural indices r,j,l select the signed numerator exponent (s+k-r-l, x+a0+a1+2k+r+j+l, z+a2-j).

**Definition 1.2 (The signed binomial weight).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedWeight`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is binom(-k,r) binom(-a0,l) (-1)^j binom(-(2k+r),j). The normalization is the integer-binomial normalization of the residue reconstruction suppliers.

**Definition 1.3 (A finite fiber for every signed target).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedFiber`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ranges are r,l at most toNat(s+k) and j at most toNat(z+a2). All three signed numerator coordinates must be nonnegative. Negative target bounds therefore give empty admissible fibers without truncating an infinite numerator.

**Theorem 1.4 (Sharp cumulative bounds).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balanced_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balanced_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative numerator coordinates imply r+l at most s+k, j at most z+a2 and r+j+l at most s+z+k+a2. They also force all native cumulative target degrees to be nonnegative.

**Theorem 1.5 (Constant total numerator degree).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balanced_input_total`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balanced_input_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every numerator index in the fiber has total s+x+z+3k+a0+a1+a2.

**Theorem 1.6 (Exact membership).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.mem_balancedFiber_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.mem_balancedFiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A natural triple belongs to the finite fiber exactly when all three signed numerator coordinates are nonnegative.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedFiber`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedInput`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balancedWeight`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balanced_bounds`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.balanced_input_total`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber.mem_balancedFiber_iff`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber](ThreeFieldInnerLaurentFiber.md)
