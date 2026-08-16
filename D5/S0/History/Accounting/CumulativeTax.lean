/- GID: D5/S0/History/Accounting/CumulativeTax
   generality: G
   mirror-B: D5/B/S0/History/Accounting/CumulativeTax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stepwise additive taxes accumulate to the terminal balance. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- Library-search audit trail (2026-08-16):
   * Repository searches for telescoping, stepwise taxes, and cumulative accounting found
     applications of telescoping sums but no declaration of this recurrence theorem.
   * Pinned Mathlib and Loogle both returned the exact upstream telescoping lemma
     `Finset.sum_range_sub`; the proof below applies it directly.
   * The skill `smart_search.sh` text queries exited 1 without a declaration-name match. -/

namespace D5.S0.History.Accounting.CumulativeTax

open scoped BigOperators

/-- If every transition adds its tax to the current balance, the terminal balance is the
initial balance plus the sum of all preceding taxes. -/
theorem terminal_balance_eq_initial_add_tax
    {G : Type*} [AddCommGroup G] (balance tax : Nat -> G)
    (step : forall i, balance (i + 1) = balance i + tax i) (n : Nat) :
    balance n = balance 0 + ∑ i ∈ Finset.range n, tax i := by
  have tax_eq (i : Nat) : tax i = balance (i + 1) - balance i := by
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using (step i).symm
  calc
    balance n = balance 0 + (balance n - balance 0) := by simp
    _ = balance 0 + ∑ i ∈ Finset.range n, (balance (i + 1) - balance i) := by
      rw [Finset.sum_range_sub]
    _ = balance 0 + ∑ i ∈ Finset.range n, tax i := by
      congr 1
      exact Finset.sum_congr rfl fun i _ => (tax_eq i).symm

end D5.S0.History.Accounting.CumulativeTax
