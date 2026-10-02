/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveATree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveATree
   mirror-E: none(waiver:ranked-a-tree-enumeration)
   anchors: [mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: Ranked A paths satisfy a coupled Fibonacci count by disjoint child decomposition. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveATree

inductive Label
  | D | E | P | Q
  deriving DecidableEq

def Paths : ℕ → Label → Type
  | 0, _ => Unit
  | depth + 1, .D => Paths depth .D ⊕ Paths depth .P
  | depth + 1, .E => Paths depth .D ⊕ Paths depth .E
  | depth + 1, .P => Paths depth .Q ⊕ (Paths depth .E ⊕ Paths depth .P)
  | depth + 1, .Q => Paths depth .Q ⊕ (Paths depth .P ⊕ Paths depth .P)


theorem A_path_enumeration (depth : ℕ) :
    Nat.card (Paths depth .D) = Nat.fib (2 * depth + 1) := by
  have hfinite : ∀ count label, Fintype (Paths count label) := by
    intro count
    induction count with
    | zero => intro label; exact inferInstanceAs (Fintype Unit)
    | succ count ih =>
      letI : ∀ label, Fintype (Paths count label) := ih
      intro label
      cases label <;> dsimp [Paths] <;> infer_instance
  letI : ∀ count label, Fintype (Paths count label) := hfinite
  have hinvariant : ∀ count,
      Nat.card (Paths count .D) = Nat.fib (2 * count + 1) ∧
      Nat.card (Paths count .P) = Nat.fib (2 * count + 2) ∧
      Nat.card (Paths count .E) + Nat.card (Paths count .Q) =
        Nat.card (Paths count .D) + Nat.card (Paths count .P) := by
    intro count
    induction count with
    | zero => simp [Paths, Nat.card_eq_fintype_card]
    | succ count ih =>
      have hD : Nat.card (Paths (count + 1) .D) =
          Nat.card (Paths count .D) + Nat.card (Paths count .P) := by
        simp only [Paths, Nat.card_sum]
      have hE : Nat.card (Paths (count + 1) .E) =
          Nat.card (Paths count .D) + Nat.card (Paths count .E) := by
        simp only [Paths, Nat.card_sum]
      have hP : Nat.card (Paths (count + 1) .P) =
          Nat.card (Paths count .Q) +
            (Nat.card (Paths count .E) + Nat.card (Paths count .P)) := by
        simp only [Paths, Nat.card_sum]
      have hQ : Nat.card (Paths (count + 1) .Q) =
          Nat.card (Paths count .Q) +
            (Nat.card (Paths count .P) + Nat.card (Paths count .P)) := by
        simp only [Paths, Nat.card_sum]
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
      · rw [hD, ih.1, ih.2.1, hodd]
      · rw [hP, heven]
        omega
      · rw [hD, hE, hP, hQ]
        omega
  exact (hinvariant depth).1

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveATree
