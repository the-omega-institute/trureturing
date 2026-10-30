# Physical multiplicities and low-denomination budgets

## Abstract

Physical multiplicities and low-denomination budgets.

**Theorem 1.1 (Physical multiplicities and low-denomination budgets).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicResetDenominations.low_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/DyadicResetDenominations.low_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive m and natural r and q<=m, the sum of 2^(i mod m) over all physical labels i in Fin(m*r) with i mod m<q equals r*(2^q-1). The sum includes all r distinct occurrences of each denomination. The proof fibers by the physical residue, uses residue_card from the source owner, and evaluates the geometric sum. Missing bins, zero r and q=0 are not excluded.

For native m>=3,r>=1, positive, top and reset labels are classified by their original residue. The two LARGE classes each have r occurrences, so total LARGE weight is 2*r. large_used_counts counts exactly the consumed top and reset occurrences of any list. These identities feed both the arbitrary-word augmentation and the universal competitor obstruction.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicResetDenominations.low_mass`
- Dependency: [D5/S3/Combinatorics/Circle/DyadicResetSource](DyadicResetSource.md)
