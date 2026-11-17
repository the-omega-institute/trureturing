# The exact sweep dimension

## Abstract

Every finite poset has sweep dimension equal to its maximum three-chain-free cardinality.

**Theorem 1.1 (The maximum bounds each eligible set).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Upper.card_le_theta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Upper.card_le_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinality of every three-chain-free subset is at most theta.

**Theorem 1.2 (A sweep system with theta orders).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Upper.exists_sweep_theta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Upper.exists_sweep_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A chain cover of the product with the two-element chain supplies the orders. In each chain, lower-layer points come first in reverse order, then upper-layer points in forward order, then the remaining points. A point in both layers is automatically first in its lower-layer block. Convexity prevents an interval omitting y from containing points both strictly below and strictly above y. The two layers therefore supply the required order for every interval and outsider.

**Definition 1.3 (The minimum size of a sweep system).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Upper.sweepDimension`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/Upper.sweepDimension` (`✓ std3`).

*Citation.* Paolo Boldi; Sebastiano Vigna (2026). *The lattice of antichains of intervals: Dyck paths, level sets, and sweep dimension*. DOI: [10.48550/arXiv.2610.41385](https://doi.org/10.48550/arXiv.2610.41385). URL: <https://arxiv.org/abs/2610.41385v1>.

*Commentary.*

Sweep dimension is the least natural number k admitting a k-order sweep system, following Boldi–Vigna, Definition 1. The orders are arbitrary linear orders, repetitions are allowed, and every order-convex subset is an interval, including the empty and full subsets. This formalization also includes empty and singleton carriers.

**Theorem 1.4 (Sweep dimension equals theta).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/Upper.sweepDimension_eq_theta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/Upper.sweepDimension_eq_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite poset, sweep dimension is exactly theta. The construction gives the upper bound, and the convex-hull injection gives the lower bound. For carriers with at least two points this is the general identity used in the endpoint classifications.

## References

- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Upper.card_le_theta`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Upper.exists_sweep_theta`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Upper.sweepDimension`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/Upper.sweepDimension_eq_theta`
- Dependency: [D5/S3/Combinatorics/SweepDimension/Basic](Basic.md)
- Dependency: [D5/S3/Combinatorics/SweepDimension/FiniteDilworth](FiniteDilworth.md)
