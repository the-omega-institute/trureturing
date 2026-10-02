/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveBTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveBTree
   mirror-E: none(waiver:ranked-b-tree-enumeration)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Disjoint ranked B paths obey a uniform label identity and Fibonacci root counts. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveBTree

inductive Label
  | L
  | M (sites : ℕ)
  | R (sites : ℕ)

def Paths : ℕ → Label → Type
  | 0, _ => Unit
  | depth + 1, .L => Paths depth .L ⊕ Paths depth (.M 3)
  | depth + 1, .M sites =>
      (Paths depth .L ⊕ (Σ edge : Fin (sites - 2), Paths depth (.R (edge.val + 2)))) ⊕
        Paths depth (.M (sites + 1))
  | depth + 1, .R sites =>
      Paths depth .L ⊕ (Σ edge : Fin (sites - 1), Paths depth (.R (edge.val + 2)))


set_option maxHeartbeats 1200000 in
theorem B_path_enumeration (depth : ℕ) :
    Nat.card (Paths depth .L) = Nat.fib (2 * depth + 1) := by
  have hfinite : ∀ count label, Fintype (Paths count label) := by
    intro count
    induction count with
    | zero => intro label; exact inferInstanceAs (Fintype Unit)
    | succ count ih =>
      letI : ∀ label, Fintype (Paths count label) := ih
      intro label
      cases label <;> dsimp [Paths] <;> infer_instance
  letI : ∀ count label, Fintype (Paths count label) := hfinite
  have hcompare : ∀ count sites, 3 ≤ sites →
      Nat.card (Paths (count + 1) (.M sites)) =
        Nat.card (Paths (count + 1) (.R (sites - 1))) +
          Nat.card (Paths count (.M (sites + 1))) := by
    intro count sites _
    simp only [Paths, Nat.card_sum, Nat.card_sigma]
    rw [show sites - 1 - 1 = sites - 2 by omega]
  have hRdiff : ∀ count sites, 3 ≤ sites →
      Nat.card (Paths (count + 1) (.R sites)) =
        Nat.card (Paths (count + 1) (.R (sites - 1))) +
          Nat.card (Paths count (.R sites)) := by
    intro count sites hsites
    have hsum : (∑ edge : Fin (sites - 1),
        Nat.card (Paths count (.R (edge.val + 2)))) =
        (∑ edge : Fin (sites - 2), Nat.card (Paths count (.R (edge.val + 2)))) +
          Nat.card (Paths count (.R sites)) := by
      rw [show sites - 1 = sites - 2 + 1 by omega, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, show sites - 2 + 2 = sites by omega]
    simp only [Paths, Nat.card_sum, Nat.card_sigma]
    rw [show sites - 1 - 1 = sites - 2 by omega]
    rw [hsum, Nat.add_assoc]
  have hinvariant : ∀ count,
      Nat.card (Paths count .L) = Nat.fib (2 * count + 1) ∧
      Nat.card (Paths count (.M 3)) = Nat.fib (2 * count + 2) ∧
      (∀ sites, 3 ≤ sites →
        Nat.card (Paths count (.M (sites + 1))) +
          Nat.card (Paths count (.R (sites - 1))) =
            2 * Nat.card (Paths count (.M sites))) := by
    intro count
    induction count with
    | zero => simp [Paths, Nat.card_eq_fintype_card]
    | succ count ih =>
      have hL : Nat.card (Paths (count + 1) .L) =
          Nat.card (Paths count .L) + Nat.card (Paths count (.M 3)) := by
        simp only [Paths, Nat.card_sum]
      have hM : Nat.card (Paths (count + 1) (.M 3)) =
          Nat.card (Paths count .L) + 2 * Nat.card (Paths count (.M 3)) := by
        have hc := hcompare count 3 (by omega)
        have hr : Nat.card (Paths (count + 1) (.R 2)) =
            Nat.card (Paths count .L) + Nat.card (Paths count (.R 2)) := by
          simp only [Paths, Nat.card_sum, Nat.card_sigma, Nat.reduceSub,
            Fin.sum_univ_one, Fin.val_zero, Nat.zero_add]
        have hu := ih.2.2 3 (by omega)
        simp only [Nat.reduceSub, Nat.reduceAdd] at hc hu
        omega
      have hodd : Nat.fib (2 * (count + 1) + 1) =
          Nat.fib (2 * count + 1) + Nat.fib (2 * count + 2) := by
        simpa only [show 2 * (count + 1) + 1 = 2 * count + 1 + 2 by omega,
          show 2 * count + 1 + 1 = 2 * count + 2 by omega] using
          (Nat.fib_add_two (n := 2 * count + 1))
      have heven : Nat.fib (2 * (count + 1) + 2) =
          Nat.fib (2 * count + 1) + 2 * Nat.fib (2 * count + 2) := by
        have hrec := Nat.fib_add_two (n := 2 * count + 2)
        have heq : 2 * count + 2 + 1 = 2 * (count + 1) + 1 := by omega
        rw [heq, hodd] at hrec
        rw [show 2 * (count + 1) + 2 = 2 * count + 2 + 2 by omega]
        omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hL, ih.1, ih.2.1, hodd]
      · rw [hM, ih.1, ih.2.1, heven]
      · intro sites hsites
        have hfirst := hcompare count sites hsites
        have hsecond := hcompare count (sites + 1) (by omega)
        have hthird := hRdiff count sites hsites
        have hprevious := ih.2.2 (sites + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hsecond hprevious
        omega
  exact (hinvariant depth).1

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveBTree
