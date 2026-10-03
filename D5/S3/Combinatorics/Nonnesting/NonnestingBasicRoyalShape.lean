/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape
   mirror-E: none(waiver:royal-dyck-shape)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff, mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Extracts Dyck steps by tracking the letters with odd occurrence count. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalEncoding
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape

open scoped symmDiff
open DyckStep

local notation "toggle" =>
  (fun (active : Finset ℕ) (letter : ℕ) => active ∆ Singleton.singleton letter)
def scan (s : Finset ℕ) : List ℕ → List DyckStep
  | [] => []
  | a :: w =>
      if a ∈ s then D :: scan (toggle s a) w else U :: scan (toggle s a) w
def shape (p w : List ℕ) (hw : w.Perm (p.flatMap fun a => [a, a])) : DyckWord := by
  classical
  have scan_balance (s : Finset ℕ) (w : List ℕ) :
      (scan s w).count D + (w.foldl toggle s).card =
        (scan s w).count U + s.card := by
    have toggle_eq (active : Finset ℕ) (letter : ℕ) :
        toggle active letter =
          if letter ∈ active then active.erase letter else insert letter active := by
      ext value
      by_cases present : letter ∈ active <;>
        simp [Finset.mem_symmDiff, present] <;> grind
    induction w generalizing s with
    | nil => simp [scan]
    | cons a w ih =>
      by_cases h : a ∈ s
      · have ht : toggle s a = s.erase a := by simp [toggle_eq, h]
        have hc := Finset.card_erase_add_one h; have htail := ih (toggle s a)
        simp only [scan, h, ite_true, List.count_cons, beq_iff_eq,
          reduceCtorEq, ite_true, ite_false, List.foldl_cons] at *
        rw [ht] at htail ⊢; omega
      · have ht : toggle s a = insert a s := by simp [toggle_eq, h]
        have hc := Finset.card_insert_of_notMem h; have htail := ih (toggle s a)
        simp only [scan, h, ite_false, List.count_cons, beq_iff_eq,
          reduceCtorEq, ite_true, List.foldl_cons] at *
        rw [ht] at htail ⊢; omega
  have scan_take (s : Finset ℕ) (w : List ℕ) (i : ℕ) :
      (scan s w).take i = scan s (w.take i) := by
    induction w generalizing s i with
    | nil => simp [scan]
    | cons a w ih =>
      cases i with
      | zero => simp [scan]
      | succ i =>
        by_cases h : a ∈ s <;> simp [scan, h, ih]
  have hpair : ∀ (s : Finset ℕ) (p : List ℕ),
      (p.flatMap fun a => [a, a]).foldl toggle s = s := by
    intro s p
    induction p generalizing s with
    | nil => rfl
    | cons a p ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [symmDiff_symmDiff_cancel_right, ih]
  haveI : RightCommutative toggle :=
    ⟨fun active first second => symmDiff_right_comm active {first} {second}⟩
  have hfold : w.foldl toggle ∅ = ∅ := by
    rw [hw.foldl_eq]; exact hpair ∅ p
  refine ⟨scan ∅ w, ?_, ?_⟩
  · have h := scan_balance ∅ w
    simp [hfold] at h; omega
  · intro i
    rw [scan_take]; have h := scan_balance ∅ (w.take i); simp at h; omega
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalShape.shape
