# Typed Port Transport

## Definition 1.1: Route endpoint kinds

`RouteKind` has the three endpoint types `ll`, `hh`, and `lh`. A finite routing path has exactly one of these types.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteKind`.

## Definition 1.2: Finite route endpoint ledger

`RouteEndpoints` records a finite type of paths, its endpoint kind, the number of left and slack terminals on each path, and the two endpoint totals. An `ll` path contributes two left terminals, an `hh` path contributes two slack terminals, and an `lh` path contributes one of each.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.RouteEndpoints`.

## Definition 1.3: Partial matching endpoint sets

For two finite simple graphs on the same port type, `leftTerminalsOf` is the set of ports with actual degree one and pairing degree zero, while `slackTerminalsOf` is the set with actual degree zero and pairing degree one. These sets are computed from the matching graphs themselves.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.leftTerminalsOf`, `D5/S3/Combinatorics/Graph/TypedPortTransport.slackTerminalsOf`.

## Theorem 1.4: Partial matching balance

Let `actual` and `pairing` be finite simple matching graphs on the same port type. The difference of twice their edge counts equals the difference between the computed left and slack terminal counts. The proof uses the degree sum theorem and a pointwise classification of the possible degree pairs `(0,0)`, `(1,0)`, `(0,1)`, and `(1,1)`.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.matching_defect_eq_terminal_difference` (internal proof witness).

## Theorem 1.5: Typed port defect identity

For every finite route endpoint ledger and two finite matching graphs whose computed terminal sets agree with its endpoint totals, if `a`, `b`, and `c` count `ll`, `hh`, and `lh` paths respectively, then

\[
  C-R=a-b.
\]

The proof first derives `ell=2a+c` and `slack=2b+c` by finite endpoint counting. It then applies the partial-matching degree balance and combines the two equations; no nonnegativity or truncated subtraction is used because the identity is stated in `\mathbb Z`.

*Formalization.* `D5/S3/Combinatorics/Graph/TypedPortTransport.defect_eq_route_difference`.

*Source.* `docs/develop/theory/RECTANGULAR_GRID_PARITY_TRANSPORT.md`, Theorem 4.3. The Lean theorem formalizes the generic typed-port counting core; the geometric construction of a particular grid routing remains a separate obligation.
