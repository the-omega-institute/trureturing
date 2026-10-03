# Typed port transport and the defect identity

## Abstract

A finite typed port routing has LL, HH and LH path types. Endpoint counting gives ell=2a+c and slack=2b+c. Two partial matching graphs on the same finite port type compute these terminal sets from their degree pairs; the signed difference of their edge counts then equals a-b.

**Definition 1.1 (Endpoint types).**

Lean statement: `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteKind`

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteKind` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RouteKind distinguishes LL, HH and LH paths. The labels record endpoint types and do not identify a graph embedding or a choice of local pairing.

**Definition 1.2 (Finite endpoint ledger).**

Lean statement: `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteEndpoints`

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteEndpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RouteEndpoints contains a finite path type, its endpoint kind, per-path left and slack terminal counts, and their totals. LL contributes (2,0), HH contributes (0,2), and LH contributes (1,1).

**Theorem 1.3 (Partial matching balance).**

Lean statement: `D5/S3/Combinatorics/Graph/TypedPortTransport.matching_defect_eq_terminal_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TypedPortTransport.matching_defect_eq_terminal_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both graph degrees are at most one, twice the actual edge count minus twice the pairing edge count equals the difference between the computed (1,0) and (0,1) terminal counts. The proof classifies all degree pairs pointwise and applies the finite graph degree-sum theorem.

**Theorem 1.4 (Endpoint counting).**

Lean statement: `D5/S3/Combinatorics/Graph/TypedPortTransport.terminal_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TypedPortTransport.terminal_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite endpoint ledger forces ell=2 card(LL)+card(LH) and slack=2 card(HH)+card(LH).

**Theorem 1.5 (Typed port defect identity).**

Lean statement: `D5/S3/Combinatorics/Graph/TypedPortTransport.defect_eq_route_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TypedPortTransport.defect_eq_route_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the endpoint totals of the route and matching ledgers agree, then (C:R viewed in integers) satisfies C-R=card(LL)-card(HH). The proof combines endpoint counting with the partial-matching degree balance.

The statement is the generic counting core of the port-routing defect identity. It does not claim that an arbitrary finite graph admits the geometric routing hypotheses used by a rectangular-grid application.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteEndpoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteKind`
- Truth anchor: `D5/S3/Combinatorics/Graph/TypedPortTransport.defect_eq_route_difference`
- Truth anchor: `D5/S3/Combinatorics/Graph/TypedPortTransport.matching_defect_eq_terminal_difference`
- Truth anchor: `D5/S3/Combinatorics/Graph/TypedPortTransport.terminal_counts`
