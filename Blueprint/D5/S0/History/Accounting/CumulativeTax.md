# Cumulative Tax Accounting

## Abstract

Stepwise additive taxes accumulate to the terminal balance.

**Theorem 1.1 (Stepwise taxes accumulate to the terminal balance).**

$$(\forall i, S_{i+1} = S_{i} + tau_{i}) \Rightarrow S_{n} = S_{0} + \sum_{i< n} tau_{i}.$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Accounting/CumulativeTax.terminal_balance_eq_initial_add_tax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S and tau be sequences in a commutative additive group. If each successive balance is the preceding balance plus the tax at that step, then the balance at time n is the initial balance plus the sum of all taxes at times strictly before n.

Pinned Mathlib and Loogle supplied Finset.sum_range_sub. The Lean proof rewrites each tax as a consecutive balance difference and applies that upstream telescoping lemma directly.

## References

- Truth anchor: `D5/S0/History/Accounting/CumulativeTax.terminal_balance_eq_initial_add_tax`
