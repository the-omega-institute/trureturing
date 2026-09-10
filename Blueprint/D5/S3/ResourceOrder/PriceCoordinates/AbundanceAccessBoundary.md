# Abundance and Monetary Access

## Abstract

Arbitrary reproducible output and self-supplied operating energy do not determine whether money controls access.

**Theorem 1.1 (Abundant goods can coexist with paid scarce access).**

Lean statement: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.abundance_preserves_paid_access_difference`

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.abundance_preserves_paid_access_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The model admits every natural quantity of the first good, balances harvested energy against its operating requirement, and allows at most one reservation of a second good. Charging one unit for the reservation gives strictly more access at wealth one than at wealth zero. This is an inhabited logical countermodel, not an engineering construction of autonomous AI or a prediction of future prices. Arbitrarily large finite output is not actual infinite output at a finite time.

**Theorem 1.2 (Productive abundance alone does not erase monetary access).**

Lean statement: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.not_abundance_makes_wealth_irrelevant`

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.not_abundance_makes_wealth_irrelevant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The countermodel refutes the universal inference from energy adequacy and arbitrary reproducible output to wealth-independent access under an otherwise unconstrained price rule. It does not establish that money must survive, or that monetary allocation is desirable.

**Theorem 1.3 (Free admissible choices are independent of wealth).**

Lean statement: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_access_ignores_wealth`

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_access_ignores_wealth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every admissible choice actually has zero required payment, every nonnegative wealth gives exactly that admissible set. Universal satisfaction additionally requires all jointly feasible desired choices to be in the set. This does not model taxes, outstanding debts, accounting, status, personal meaning, or who controls eligibility.

**Theorem 1.4 (A nonmonetary capacity rule still restricts choices).**

Lean statement: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_rationing_retains_capacity_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_rationing_retains_capacity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With zero charges and any natural capacity, every nonnegative wealth gives the same capacity-limited set. Demand exceeding capacity remains unavailable. Scarcity is thus compatible with nonmonetary limits. Selecting between competing people's claims requires an additional social rule, which this single-person menu does not determine.

## References

- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.abundance_preserves_paid_access_difference`
- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_access_ignores_wealth`
- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_rationing_retains_capacity_bound`
- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.not_abundance_makes_wealth_irrelevant`
- Dependency: [D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess](ThresholdAccess.md)
