# Actual disjoint carriers with vanishing norm error

## Abstract

Actual disjoint carriers with vanishing norm error

**Theorem 1.1 (Actual disjoint carriers with vanishing norm error).**

Lean statement: `D5/S3/Topology/Measures/L1Disjointization.exists_disjoint_restrictions`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Disjointization.exists_disjoint_restrictions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. Let f be any real L1 sequence, A any sequence of measurable sets, and alpha any real. Suppose for all i < h the norm of f(i) restricted to A(h) is at most (1/2)^h, and the norms of the restrictions to A(i) tend to alpha. There are actual measurable E(i), pairwise disjoint as sets, such that the norms of the literal restrictions to E(i) still tend to alpha, and the norms of the differences between the literal complementary restrictions for E(i) and for A(i) tend to zero. Explicitly E(i) is A(i) minus the union of every later A(h). The nonnegative countable-union integral bound makes the removed mass at most (1/2)^i. No finite-measure hypothesis is required.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1Disjointization.exists_disjoint_restrictions`
- Dependency: [D5/S3/Topology/Measures/L1Restriction](L1Restriction.md)
