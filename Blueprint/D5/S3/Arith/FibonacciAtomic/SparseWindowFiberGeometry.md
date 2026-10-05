# Sparse Window Fibres

## Abstract

The geometry of sparse Fibonacci window labels on the circle.

**Definition 1.1 (Time tuple fibres).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.fiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A time tuple fibre is the intersection of the window arcs translated back by their retained observation times. The regular domain removes precisely the translated window cuts.

**Theorem 1.2 (Fibres and connected components).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.sparse_window_fiber_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.sparse_window_fiber_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For width at least two and a nonempty finite set of times, every nonempty tuple fibre equals a connected component of the regular domain. A component determines its tuple uniquely, and each regular point has one tuple. The number of distinct circle cuts equals the number of their natural indices. Every nonempty fibre contains a golden phase with natural index above any given bound. The phase visits refer to circle rotation; identification with canonical natural digit rows is an additional relation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.fiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry.sparse_window_fiber_geometry`
- Dependency: [D5/S1/Digit/Infinite/SparseWindowMutualDetermination](../../../S1/Digit/Infinite/SparseWindowMutualDetermination.md)
- Dependency: [D5/S1/Phase/Basic](../../../S1/Phase/Basic.md)
