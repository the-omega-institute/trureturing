/- GID: D5/S1/Recurrence/FiniteCompanionDefect
   generality: G
   mirror-B: D5/B/S1/Recurrence/FiniteCompanionDefect
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Constructive additive elimination of a finite reset companion defect. -/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.FiniteCompanionDefect
open scoped BigOperators
variable {A : Type*} [AddCommGroup A]

/-- Solve the adjacent equations, with a prescribed initial coordinate. -/
def reconstruct : (n : ℕ) → A → (Fin n → A) → (Fin (n + 1) → A)
  | 0, a, _ => fun _ => a
  | n + 1, a, t => Fin.cons a (reconstruct n (t 0 - a) (fun j => t j.succ))

private theorem reconstruct_head (n : ℕ) (a : A) (t : Fin n → A) :
    reconstruct n a t 0 = a := by
  cases n <;> rfl

private theorem reconstruct_adjacent (n : ℕ) (a : A) (t : Fin n → A) (j : Fin n) :
    reconstruct n a t j.succ + reconstruct n a t j.castSucc = t j := by
  induction n generalizing a with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [reconstruct, reconstruct_head]
      · simpa only [reconstruct, Fin.cons_succ, Fin.castSucc_succ] using
          ih (t 0 - a) (fun k => t k.succ) k

private theorem reconstruct_unique (n : ℕ) (v : Fin (n + 1) → A) :
    reconstruct n (v 0) (fun j => v j.succ + v j.castSucc) = v := by
  induction n with
  | zero => ext j; fin_cases j; rfl
  | succ n ih =>
      have ht : (fun j : Fin (n + 1) => v j.succ + v j.castSucc) 0 - v 0 =
          v (0 : Fin (n + 1)).succ := by simp
      simp only [reconstruct, ht]
      have hi := ih (fun j : Fin (n + 1) => v j.succ)
      simp only [Fin.succ_castSucc] at hi
      rw [hi]
      exact Fin.cons_self_tail v

/-- Integral triangular coordinates: the initial value and all adjacent sums. -/
def domainEquiv (n : ℕ) : (Fin (n + 1) → A) ≃+ A × (Fin n → A) where
  toFun v := (v 0, fun j => v j.succ + v j.castSucc)
  invFun z := reconstruct n z.1 z.2
  left_inv := reconstruct_unique n
  right_inv z := by
    apply Prod.ext
    · exact reconstruct_head n z.1 z.2
    · funext j; exact reconstruct_adjacent n z.1 z.2 j
  map_add' v w := by
    apply Prod.ext
    · rfl
    · funext j
      change (v j.succ + w j.succ) + (v j.castSucc + w j.castSucc) =
        (v j.succ + v j.castSucc) + (w j.succ + w j.castSucc)
      abel

/-- The tail coordinates whose distance from the right boundary is odd. -/
def tailSum (n : ℕ) (t : Fin n → A) : A :=
  ∑ j : Fin n, if Odd (n - j.val) then t j else 0

private theorem sum_coordinates (n : ℕ) (v : Fin (n + 1) → A) :
    (∑ j, v j) = (if Odd (n + 1) then v 0 else 0) +
      tailSum n (fun j => v j.succ + v j.castSucc) := by
  induction n with
  | zero => simp [tailSum]
  | succ n ih =>
      have hi := ih (fun j : Fin (n + 1) => v j.succ)
      rw [Fin.sum_univ_succ]
      conv_rhs => rw [tailSum, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
      change v 0 + (∑ j : Fin (n + 1), v j.succ) =
        (if Odd (n + 1 + 1) then v 0 else 0) +
        ((if Odd (n + 1) then v (0 : Fin (n + 1)).succ + v 0 else 0) +
          tailSum n (fun j => v j.succ.succ + v j.castSucc.succ))
      rw [hi]
      by_cases h : Odd (n + 1)
      · have hn : ¬ Odd (n + 1 + 1) := by simp only [Nat.odd_iff] at *; omega
        simp only [h, hn, if_true, if_false, zero_add]; abel
      · have hn : Odd (n + 1 + 1) := by simp only [Nat.odd_iff] at *; omega
        simp only [h, hn, if_true, if_false, zero_add]

/-- Identity plus the right-row reset companion, without an involution premise. -/
def companion (J : A →+ A) (n : ℕ) : (Fin (n + 1) → A) →+ (Fin (n + 1) → A) where
  toFun v := Fin.cons (v 0 + J (∑ j, v j)) (fun j => v j.succ + v j.castSucc)
  map_zero' := by ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp
  map_add' v w := by
    ext j; refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero, Pi.add_apply, Finset.sum_add_distrib, map_add]; abel
    · simp only [Fin.cons_succ, Pi.add_apply]; abel

/-- A shear of the codomain, independent of the triangular domain coordinates. -/
def codomainEquiv (J : A →+ A) (n : ℕ) :
    (Fin (n + 1) → A) ≃+ A × (Fin n → A) where
  toFun y := (y 0 - J (tailSum n (fun j => y j.succ)), fun j => y j.succ)
  invFun z := Fin.cons (z.1 + J (tailSum n z.2)) z.2
  left_inv y := by
    simp only [sub_add_cancel]
    exact Fin.cons_self_tail y
  right_inv z := by
    apply Prod.ext
    · change (z.1 + J (tailSum n z.2)) - J (tailSum n z.2) = z.1
      exact add_sub_cancel_right _ _
    · rfl
  map_add' y z := by
    apply Prod.ext
    · change (y 0 + z 0) - J (tailSum n (fun j => y j.succ + z j.succ)) = _
      have hs : tailSum n (fun j => y j.succ + z j.succ) =
          tailSum n (fun j => y j.succ) + tailSum n (fun j => z j.succ) := by
        simp only [tailSum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      change (y 0 + z 0) - J (tailSum n (fun j => y j.succ + z j.succ)) =
        (y 0 - J (tailSum n (fun j => y j.succ))) +
          (z 0 - J (tailSum n (fun j => z j.succ)))
      rw [hs, map_add]; abel
    · rfl

/-- Separately defined domain and codomain equivalences reduce the full companion to
identity on the tail and `a ↦ a + J a` (odd length) or identity (even length). -/
theorem eliminate (J : A →+ A) (n : ℕ) (v : Fin (n + 1) → A) :
    codomainEquiv J n (companion J n v) =
      ((domainEquiv n v).1 + J (if Odd (n + 1) then (domainEquiv n v).1 else 0),
        (domainEquiv n v).2) := by
  apply Prod.ext
  · change (v 0 + J (∑ j, v j)) -
        J (tailSum n (fun j => v j.succ + v j.castSucc)) = _
    rw [sum_coordinates, map_add]
    change (v 0 + (J (if Odd (n + 1) then v 0 else 0) + _)) - _ =
      v 0 + J (if Odd (n + 1) then v 0 else 0)
    abel
  · rfl

end D5.S1.Recurrence.FiniteCompanionDefect
