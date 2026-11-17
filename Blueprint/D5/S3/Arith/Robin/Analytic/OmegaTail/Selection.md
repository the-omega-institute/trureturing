# Selecting prime sets with exact total size

## Abstract

Actual prime capacities and exact second-order cardinality adjustment for finite density selections.

**Theorem 1.1 (Capacity of a logarithmic prime window).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.primeInterval_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.primeInterval_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed 0<a<b, the number of primes in (a*log(x),b*log(x)], divided by y(x)=log(x)/log(log(x)), tends to b-a. The existing prime number theorem is applied separately to both endpoints. Natural floors represent the same actual real-endpoint window.

**Definition 1.2 (Exact count above the threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.selectedCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.selectedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected count K(lambda,x) is floor(T(lambda,x))+1. Its strict relation to the real threshold is retained. The second-order cancellation (K*log(log(x))-log(x))/y tends to lambda; the error is controlled by log(log(x))/y tending to zero.

**Definition 1.3 (One box absorbs the integer adjustment).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every box except one receives floor(r_j*y) primes. The distinguished box receives K minus the sum in the other boxes. This is a natural number by truncated subtraction, and the subsequent theorems prove that the truncation is eventually inactive.

**Theorem 1.4 (Exact total and limiting occupancies).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of nonnegative masses summing to one, with strictly positive mass in the distinguished box, the adjusted occupancies eventually sum exactly to K. Each occupancy divided by y tends to its prescribed mass. The distinguished box has linear slack, whereas rounding and the second-order shift are negligible on that scale.

**Theorem 1.5 (Every selected count fits the available primes).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_fits`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_fits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each actual capacity divided by y tends to d_j and r_j<d_j, then eventually all adjusted occupancies fit their capacities simultaneously. Finiteness permits one common cutoff for all boxes.

**Theorem 1.6 (Strict logarithmic slack pays the full product budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive upper endpoints b_j and lambda+sum(r_j*log(b_j))<0, eventually sum(k_j*log(b_j*log(x)))<log(x). The exact cancellation K*log(log(x))=log(x)+lambda*y+o(y) is used; the weaker leading relation K/y tending to one would not justify this conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_budget`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_fits`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.adjustedSelection_spec`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.primeInterval_capacity`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Selection.selectedCount`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)
