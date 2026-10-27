/- GID: D5/S1/Words/Compositions/WisemanA388712
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/WisemanA388712
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonchoosable partitions and nonsuperdiagonal reversed partitions have equal counts. -/

/-
admission_basis: open-problem-resolution (#18601; Proved)
escape_witness: none
result: proof_shape: bind-only; consumer: none (settling result).
sorted_choosable_iff_superdiagonal: proof_shape: bind-only;
  consumers: WisemanA388712.result, WisemanA387118.result, WisemanA388713.result.
Direct frozen dependencies (same-delivery helpers expanded):
  D5/S1/Words/Compositions/ChoosableInitialIntervals.ChoosableInitial
    statement_id: sha256:08406afdbaec81eb130adc1789a5e89e8e9e34d26f75c1f79f08565cd7e53f77
  D5/S1/Words/Compositions/ChoosableInitialIntervals.Superdiagonal
    statement_id: sha256:fde0ce5426700b449298459172edd4fcc27f13ac28cbcc8d3e5eb192012180c6
  D5/S1/Words/Compositions/ChoosableInitialIntervals.choosableInitial_congr_perm
    statement_id: sha256:860abfb620b8e725881fac6bea668347eeef5ca8ffc5814cb0ce44b8a0a2e8c9
  D5/S1/Words/Compositions/ChoosableInitialIntervals.choosableInitial_iff_superdiagonal
    statement_id: sha256:122df65eaff368a19a0d7dedc84a08f6381bfb0c481765fa312d6b1c8510d685
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22068
The source counts retain their literal filters and reuse the existing predicates;
no duplicate predicate or forwarding definition is introduced.
The proof uses permutation invariance and the increasing-list criterion.
-/

import D5.S1.Words.Compositions.ChoosableInitialIntervals

set_option autoImplicit false

namespace D5.S1.Words.Compositions.WisemanA388712

open D5.S1.Words.Compositions.ChoosableInitialIntervals

open scoped Classical in
/-- `T(n,k)`: the number of integer partitions of `n` into `k` parts without choosable initial
intervals. -/
noncomputable def T (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => p.parts.card = k ∧ ¬ ChoosableInitial (p.parts.sort (· ≥ ·)))).card

open scoped Classical in
/-- The number of non-superdiagonal reversed partitions of `n` into `k` parts. -/
noncomputable def nonSuperdiagonal (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => p.parts.card = k ∧ ¬ Superdiagonal (p.parts.sort (· ≤ ·)))).card

/-- The conjecture of A388712. -/
def claim : Prop := ∀ n k : ℕ, T n k = nonSuperdiagonal n k

/-- The frozen list criterion transported between the two multiset sorts. -/
theorem sorted_choosable_iff_superdiagonal (s : Multiset ℕ) :
    ChoosableInitial (s.sort (· ≥ ·)) ↔ Superdiagonal (s.sort (· ≤ ·)) := by
  have hp : (s.sort (· ≥ ·)).Perm (s.sort (· ≤ ·)) := by
    apply Multiset.coe_eq_coe.mp
    simp
  exact (choosableInitial_congr_perm hp).trans
    (choosableInitial_iff_superdiagonal _ (Multiset.pairwise_sort s (· ≤ ·)))

theorem result : WisemanA388712.claim := by
  classical
  intro n k
  unfold T nonSuperdiagonal
  congr 1
  apply Finset.filter_congr
  intro p _
  exact and_congr_right (fun _ => not_congr
    (WisemanA388712.sorted_choosable_iff_superdiagonal p.parts))

end D5.S1.Words.Compositions.WisemanA388712
