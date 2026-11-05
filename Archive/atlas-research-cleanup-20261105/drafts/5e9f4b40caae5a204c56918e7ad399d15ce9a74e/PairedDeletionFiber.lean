/-
  Research candidate: exact fibres of two labelled circular deletions.

  This file is intentionally uncompiled.  The declarations below use the
  archived D5 APIs and isolate the two list lemmas which still need a normal
  Lean pass.  No declaration here is validation evidence.
/-

import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

universe u
variable {α : Type u} [DecidableEq α]

abbrev SupportedCircle (A : Finset α) :=
  D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.SupportedCircle A

private theorem mem_support (C : Cycle α) (x : α) :
    x ∈ C.toFinset ↔ x ∈ C := by
  induction C using Quotient.inductionOn with
  | _ l => exact List.mem_toFinset

private theorem rooted {C : Cycle α} {r : α} (hr : r ∈ C) :
    ∃ L : List α, C = (r :: L : List α) := by
  induction C using Quotient.inductionOn with
  | _ W =>
    obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp (Cycle.mem_coe_iff.mp hr)
    refine ⟨Q ++ P, Cycle.coe_eq_coe.mpr ⟨P.length, ?_⟩⟩
    simpa only [List.cons_append] using List.rotate_append_length_eq P (r :: Q)

def erase (x : α) (L : List α) : List α :=
  L.filter (fun y => decide (y ≠ x))

/-- The two possible rooted words obtained by swapping an adjacent `a,b` pair.
    The common root is retained, so this is a statement about oriented cycles. -/
def adjacentSwapAt (r a b : α) (C D : Cycle α) : Prop :=
  ∃ P Q : List α,
    (C = (r :: P ++ [a,b] ++ Q : List α) ∧
      D = (r :: P ++ [b,a] ++ Q : List α)) ∨
    (C = (r :: P ++ [b,a] ++ Q : List α) ∧
      D = (r :: P ++ [a,b] ++ Q : List α))

/- The only genuinely new word lemma.  Its proof is the index argument in
   Research.md: compare the positions of `a` and `b` after each erasure. -/
theorem erase_pair_classification
    {L K : List α} {a b : α}
    (hL : L.Nodup) (hK : K.Nodup)
    (haL : a ∈ L) (hbL : b ∈ L)
    (haK : a ∈ K) (hbK : b ∈ K) (hab : a ≠ b)
    (hA : erase a L = erase a K)
    (hB : erase b L = erase b K) :
    L = K ∨ ∃ P Q : List α,
      (L = P ++ [a,b] ++ Q ∧ K = P ++ [b,a] ++ Q) ∨
      (L = P ++ [b,a] ++ Q ∧ K = P ++ [a,b] ++ Q) := by
  sorry

/- Uniqueness of the swapped word for one fixed rooted source word. -/
theorem adjacentSwapAt_unique
    {r a b : α} (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    {C D E : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup) (hE : E.Nodup)
    (hCD : adjacentSwapAt r a b C D)
    (hCE : adjacentSwapAt r a b C E) : D = E := by
  sorry

/-- Exact two-deletion classification at a chosen marker `r` outside the
    deleted pair.  The support hypotheses are the actual fixed-support model. -/
theorem paired_fiber_iff_at_root
    {A : Finset α} {r a b : α}
    (hrA : r ∈ A) (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    {C D : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) :
    (delete a C = delete a D ∧ delete b C = delete b D) ↔
      C = D ∨ adjacentSwapAt r a b C D := by
  sorry

/-- The existential form says that every unequal pair in one two-deletion
    fibre is obtained by swapping the adjacent `a,b` block. -/
theorem paired_fiber_iff
    {A : Finset α} (hA : 3 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {C D : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) :
    (delete a C = delete a D ∧ delete b C = delete b D) ↔
      C = D ∨ ∃ r ∈ A, r ≠ a ∧ r ≠ b ∧ adjacentSwapAt r a b C D := by
  sorry

/-- A fixed pair fibre contains at most two supported oriented circles.  This
    avoids a finiteness/cardinality encoding: any two non-central members are
    equal, which is the exact `≤ 2` assertion needed downstream. -/
theorem pair_fiber_at_most_two
    {A : Finset α} (hA : 3 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {C D E : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup) (hE : E.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) (sE : E.toFinset = A)
    (hDobs : delete a C = delete a D ∧ delete b C = delete b D)
    (hEobs : delete a C = delete a E ∧ delete b C = delete b E)
    (hDC : D ≠ C) (hEC : E ≠ C) : D = E := by
  sorry

end D5.S3.Combinatorics.CircularWords.PairedDeletionFiber
