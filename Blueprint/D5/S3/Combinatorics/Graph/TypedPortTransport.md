# Typed Port Transport

## Definition 1.1: Route endpoint kinds

`RouteKind` has the three endpoint types `ll`, `hh`, and `lh`. A finite routing path has exactly one of these types.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteKind`.

## Definition 1.2: Finite route endpoint ledger

`RouteEndpoints` records a finite type of paths, its endpoint kind, the number of left and slack terminals on each path, and the two endpoint totals. An `ll` path contributes two left terminals, an `hh` path contributes two slack terminals, and an `lh` path contributes one of each.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteEndpoints`.

## Definition 1.3: Incidence-capacity ledger

`CapacityLedger` records the number `C` of actual edges, the capacity sum `R`, the total degree, and the left and slack terminal totals. Its incidence equation is `2C = ell + totalDegree`; its capacity equation is `totalDegree + slack = 2R`.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.CapacityLedger`.

## Theorem 1.4: Typed port defect identity

For every finite route endpoint ledger and every incidence-capacity ledger whose terminal totals agree, if `a`, `b`, and `c` count `ll`, `hh`, and `lh` paths respectively, then

\[
  C-R=a-b.
\]

The proof first derives `ell=2a+c` and `slack=2b+c` by finite endpoint counting. It then combines these equations with the incidence and capacity ledgers; no nonnegativity or truncated subtraction is used because the identity is stated in `\mathbb Z`.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.defect_eq_route_difference`.

*Source.* `docs/develop/theory/RECTANGULAR_GRID_PARITY_TRANSPORT.md`, Theorem 4.3. The Lean theorem formalizes the generic typed-port counting core; the geometric construction of a particular grid routing remains a separate obligation.
