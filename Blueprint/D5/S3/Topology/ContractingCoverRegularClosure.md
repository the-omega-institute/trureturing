# Regular closure from a contracting open cover

## Abstract

Uniformly contracting open self-covers propagate a nonempty open patch throughout a compact metric carrier.

**Theorem 1.1 (The parametric regular closure theorem).**

Lean statement: `D5/S3/Topology/ContractingCoverRegularClosure.closure_interior_eq_of_contracting_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ContractingCoverRegularClosure.closure_interior_eq_of_contracting_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be compact in any metric space, with nonempty interior. A family f_i of open maps with one common NNReal Lipschitz constant q < 1 and exact union of images equal to K forces closure(interior K) = K. The branch index need not be finite, and no ambient completeness or properness is assumed. More generally, let C be a closed nonempty subset of K, invariant under every branch, and suppose every point of K has a branch preimage in K. Compactness of C supplies nearest points; the continuous distance to C attains a maximum M on K. A covering preimage and its nearest point give M <= q M, hence M = 0 and C = K. The nonemptiness of C is explicit because real-valued infDist of the empty set is zero. For C = closure(interior K), compactness makes C compact and contained in K. Open branches preserve the interior and Lipschitz continuity preserves its closure. In particular, the three affine prefix maps of the Tribonacci Rauzy fractal satisfy these conditions, so that fractal is the closure of its interior.

## References

- Truth anchor: `D5/S3/Topology/ContractingCoverRegularClosure.closure_interior_eq_of_contracting_cover`
