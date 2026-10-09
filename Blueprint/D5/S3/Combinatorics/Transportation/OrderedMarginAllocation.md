# Ordered natural margin allocation

## Abstract

One ordered natural allocation constructs both original margins without a feasible-table premise.

**Theorem 1.1 (Both original margins from the same prescribed scan).**

$$\forall Row \in Type, Column \in Type,\; [\operatorname{Fintype}\left(Row\right)], [\operatorname{Fintype}\left(Column\right)], [\operatorname{DecidableEq}\left(Row\right)], [\operatorname{DecidableEq}\left(Column\right)], \forall rows \in \operatorname{List}\left(Row\right), columns \in \operatorname{List}\left(Column\right), demand \in \operatorname{Arrow}\left(Row, Nat\right), capacity \in \operatorname{Arrow}\left(Column, Nat\right),\; \left(\left(\forall i \in Row,\; i \in rows\right) \land \left(\left(\forall j \in Column,\; j \in columns\right) \land \operatorname{sum}\left(demand\right) = \operatorname{sum}\left(capacity\right)\right)\right) \Rightarrow \left(\left(\forall i \in Row,\; \operatorname{rowResidual}\left(\operatorname{orderedAllocation}\left(rows, columns, demand, capacity\right), i\right) = 0 \land \operatorname{rowSum}\left(\operatorname{orderedAllocation}\left(rows, columns, demand, capacity\right), i\right) = \operatorname{value}\left(demand, i\right)\right) \land \left(\left(\forall j \in Column,\; \operatorname{columnResidual}\left(\operatorname{orderedAllocation}\left(rows, columns, demand, capacity\right), j\right) = 0 \land \operatorname{columnSum}\left(\operatorname{orderedAllocation}\left(rows, columns, demand, capacity\right), j\right) = \operatorname{value}\left(capacity, j\right)\right) \land \left(\forall past \in \operatorname{List}\left(\operatorname{Product}\left(Row, Column\right)\right), future \in \operatorname{List}\left(\operatorname{Product}\left(Row, Column\right)\right),\; \operatorname{grid}\left(rows, columns\right) = \operatorname{append}\left(past, future\right) \Rightarrow \left(\left(\forall i \in Row,\; \operatorname{rowResidual}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), i\right) + \operatorname{rowSum}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), i\right) = \operatorname{value}\left(demand, i\right)\right) \land \left(\left(\forall j \in Column,\; \operatorname{columnResidual}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), j\right) + \operatorname{columnSum}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), j\right) = \operatorname{value}\left(capacity, j\right)\right) \land \left(\left(\forall cell \in \operatorname{Product}\left(Row, Column\right),\; cell \in past \Rightarrow \left(\operatorname{rowResidual}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), \operatorname{first}\left(cell\right)\right) = 0 \lor \operatorname{columnResidual}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), \operatorname{second}\left(cell\right)\right) = 0\right)\right) \land \left(\left(\forall cell \in \operatorname{Product}\left(Row, Column\right),\; \left(\neg cell \in past\right) \Rightarrow \operatorname{tableEntry}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), cell\right) = 0\right) \land \left(\left(\forall i \in Row,\; \operatorname{rowResidual}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), i\right) \le \operatorname{value}\left(demand, i\right)\right) \land \left(\forall j \in Column,\; \operatorname{columnResidual}\left(\operatorname{runPrefix}\left(past, demand, capacity\right), j\right) \le \operatorname{value}\left(capacity, j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/OrderedMarginAllocation.ordered_allocation_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite row and column carriers, the two supplied lists contain every index. Original demands and capacities are natural numbers with equal total. Starting with a zero table, visit the full row-major rectangle. Each visit computes one pre-update minimum, subtracts it from both residuals, and adds that same value to the actual cell. Zero allocations are visited as well.

In the display, rowResidual and columnResidual are the two residual projections; rowSum and columnSum sum the recorded table over the opposite carrier. tableEntry evaluates that same table. runPrefix folds the same transition from the original demands, original capacities and zero table; grid is the list product and append is list concatenation. sum denotes the complete finite sum of the given margin function.

Every prefix preserves both original conservation equations, has zero unvisited entries, and retains an exhausted endpoint at every visited pair. Residuals do not increase under a visit. Complete-grid coverage gives complementarity at every pair. Equal residual totals then force every row and column residual to zero, yielding both original margins without a supplied feasible table or completion premise. Empty carriers and zero margins remain included.

The subgroup-factorization construction consumes this same allocation theorem for every actual double-coset rectangle, with original coefficient demands and original constant capacities.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/OrderedMarginAllocation.ordered_allocation_complete`
