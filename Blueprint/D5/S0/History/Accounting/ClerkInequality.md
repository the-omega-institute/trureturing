# The Clerk Inequalities

## Abstract

Permanent records force two lower bounds on the semantic ledger.

**Theorem 1.1 (Permanent records force the clerk inequalities).**

$$\forall r, t\in \mathbb{N}, \forall H: \operatorname{ClerkHistory}(r), r \geq 1 \Rightarrow \left(\begin{aligned}\lvert Sem_{t}\rvert \geq r \cdot M_{t}\\\land \lvert Sem_{t}\rvert \geq \lvert Sem_{0}\rvert + (r - 1) \cdot M_{t}\end{aligned}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Accounting/ClerkInequality.clerk_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite counting certificate over an append-only ledger. Its semantic snapshot contains exactly the enrolled statements outside the distinguished theorem grades, and its migration snapshot contains exactly the statements entering those grades at the next tick.

Every migration creates at least r fresh records. Each record is newly enrolled at its creation tick and remains in every later semantic snapshot. When r is at least one, the semantic count at tick t is therefore at least r times the cumulative migration count. It is also at least the initial semantic count plus r minus one times the cumulative migration count.

The first bound counts the disjoint permanent records. The second removes the migrating statements from the old snapshot, inserts the fresh records, and iterates the resulting one-step bound. Pinned Mathlib and Loogle supplied Finset.sum_range_succ, which is imported and applied to both cumulative counts. Repository searches found no existing declaration with either complete bound; LeanSearch's query endpoint returned HTTP 404.

## References

- Truth anchor: `D5/S0/History/Accounting/ClerkInequality.clerk_inequality`
- Dependency: [D5/S0/History/LedgerLimit](../LedgerLimit.md)
