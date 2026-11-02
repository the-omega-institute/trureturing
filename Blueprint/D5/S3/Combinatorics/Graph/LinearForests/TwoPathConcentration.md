# Two odd paths: the signed-Catalan shift-three series law

## Abstract

The exact signed-Catalan shift-three series law for two odd path factors, with an arbitrary residual factor.

**Theorem 1.1 (The reusable two-path series identity).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.two_path_series_concentration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.two_path_series_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p and q at least one, the actual independent-set partition series of paths of orders 2p+1 and 2q+1, after multiplication by any residual series and the integer Catalan series, differs from the order 2p+2q+1 path with one isolated vertex by X cubed times the two path tails of orders 2p-2 and 2q-2.

The proof uses the actual independent-configuration deletion recurrence on the natural-number Hasse path, the Catalan functional equation, and strong induction on the sum of the two path orders. The residual series is arbitrary and is carried through by multiplication.

A transient coefficient check compiles the exact natural-subtraction shift at every legal m. Faithful transport from an arbitrary same-carrier labelled graph to this series factorization is an integration obligation for the next delivery.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.two_path_series_concentration`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional](PathCatalanFunctional.md)
