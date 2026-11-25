/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Core

@[expose] public section

attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Nat.sub Omega.Nat.pred

namespace Omega.Nat

protected theorem zero_add (n : Nat) : Eq (Nat.add zero n) n :=
  Nat.rec (motive := fun i => Eq (Nat.add zero i) i)
    rfl (fun _ h => congrArg succ h) n

theorem succ_add (n m : Nat) : Eq (Nat.add (succ n) m) (succ (Nat.add n m)) :=
  Nat.rec (motive := fun i => Eq (Nat.add (succ n) i) (succ (Nat.add n i)))
    rfl (fun _ h => congrArg succ h) m

protected theorem add_assoc (n m k : Nat) : Eq (Nat.add (Nat.add n m) k) (Nat.add n (Nat.add m k)) :=
  Nat.rec (motive := fun i => Eq (Nat.add (Nat.add n m) i) (Nat.add n (Nat.add m i)))
    rfl (fun _ h => congrArg succ h) k

protected theorem add_comm (n m : Nat) : Eq (Nat.add n m) (Nat.add m n) :=
  Nat.rec (motive := fun i => Eq (Nat.add n i) (Nat.add i n))
    (Nat.zero_add n).symm (fun i h => (congrArg succ h).trans (succ_add i n).symm) m

protected theorem add_right_comm (n m k : Nat) : Eq (Nat.add (Nat.add n m) k) (Nat.add (Nat.add n k) m) :=
  (Nat.add_assoc n m k).trans ((congrArg (Nat.add n) (Nat.add_comm m k)).trans (Nat.add_assoc n k m).symm)

protected theorem zero_mul (n : Nat) : Eq (Nat.mul zero n) zero :=
  Nat.rec (motive := fun i => Eq (Nat.mul zero i) zero) rfl (fun _ h => h) n

theorem succ_mul (n m : Nat) : Eq (Nat.mul (succ n) m) (Nat.add (Nat.mul n m) m) :=
  Nat.rec (motive := fun i => Eq (Nat.mul (succ n) i) (Nat.add (Nat.mul n i) i))
    rfl (fun i h =>
      congrArg succ ((congrArg (fun x => Nat.add x n) h).trans (Nat.add_right_comm (Nat.mul n i) i n))) m

protected theorem mul_comm (n m : Nat) : Eq (Nat.mul n m) (Nat.mul m n) :=
  Nat.rec (motive := fun i => Eq (Nat.mul n i) (Nat.mul i n)) (Nat.zero_mul n).symm
    (fun i h => (congrArg (fun x => Nat.add x n) h).trans (succ_mul i n).symm) m

protected theorem one_mul (n : Nat) : Eq (Nat.mul (succ zero) n) n :=
  (Nat.mul_comm (succ zero) n).trans (Nat.zero_add n)

protected theorem mul_add (n m k : Nat) : Eq (Nat.mul n (Nat.add m k)) (Nat.add (Nat.mul n m) (Nat.mul n k)) :=
  Nat.rec (motive := fun i => Eq (Nat.mul n (Nat.add m i)) (Nat.add (Nat.mul n m) (Nat.mul n i)))
    rfl (fun i h => (congrArg (fun x => Nat.add x n) h).trans (Nat.add_assoc (Nat.mul n m) (Nat.mul n i) n)) k

protected theorem add_mul (n m k : Nat) : Eq (Nat.mul (Nat.add n m) k) (Nat.add (Nat.mul n k) (Nat.mul m k)) :=
  (Nat.mul_comm (Nat.add n m) k).trans ((Nat.mul_add k n m).trans
    ((congrArg (fun x => Nat.add x (Nat.mul k m)) (Nat.mul_comm k n)).trans
      (congrArg (Nat.add (Nat.mul n k)) (Nat.mul_comm k m))))

protected theorem mul_assoc (n m k : Nat) : Eq (Nat.mul (Nat.mul n m) k) (Nat.mul n (Nat.mul m k)) :=
  Nat.rec (motive := fun i => Eq (Nat.mul (Nat.mul n m) i) (Nat.mul n (Nat.mul m i))) rfl
    (fun i h => (congrArg (fun x => Nat.add x (Nat.mul n m)) h).trans (Nat.mul_add n (Nat.mul m i) m).symm) k

theorem add_succ (n m : Nat) : Eq (Nat.add n (succ m)) (succ (Nat.add n m)) := Omega.rfl

theorem add_one (n : Nat) : Eq (Nat.add n zero.succ) n.succ := Omega.rfl

protected theorem mul_zero (n : Nat) : Eq (Nat.mul n zero) zero := Omega.rfl

theorem mul_succ (n m : Nat) : Eq (Nat.mul n (succ m)) (Nat.add (Nat.mul n m) n) := Omega.rfl

protected theorem mul_one (n : Nat) : Eq (Nat.mul n (succ zero)) n := Nat.zero_add n

protected theorem add_right_cancel {n m k : Nat} (h : Eq (Nat.add n m) (Nat.add k m)) : Eq n k :=
  (Nat.rec (motive := fun i => Eq (Nat.add n i) (Nat.add k i) → Eq n k) (fun h => h)
    (fun _ ih h => ih (succ.inj h)) m) h

protected theorem add_left_cancel {n m k : Nat} : Eq (Nat.add n m) (Nat.add n k) → Eq m k := fun h =>
  Nat.add_right_cancel ((Nat.add_comm m n).trans (h.trans (Nat.add_comm n k)))

protected theorem le_total (m n : Nat) : Or (Nat.le m n) (Nat.le n m) :=
  (Nat.rec (motive := fun m => ∀ n, Or (Nat.le m n) (Nat.le n m))
    (fun n => Or.inl (zero_le n))
    (fun m ih n => Nat.rec (motive := fun n => Or (Nat.le (succ m) n) (Nat.le n (succ m)))
      (Or.inr (zero_le (succ m))) (fun n _ =>
        (ih n).elim (fun h => Or.inl (succ_le_succ h)) (fun h => Or.inr (succ_le_succ h))) n) m) n

protected theorem add_le_add_left {n m : Nat} (h : Nat.le n m) (k : Nat) : Nat.le (Nat.add k n) (Nat.add k m) :=
  have right : ∀ x₀, Nat.le (Nat.add n x₀) (Nat.add m x₀) :=
    fun x₀ => Nat.rec (motive := fun x₀ => Nat.le (Nat.add n x₀) (Nat.add m x₀)) h
      (fun _ ih => succ_le_succ ih) x₀
  Eq.subst (motive := fun x => Nat.le x (Nat.add k m)) (Nat.add_comm n k)
    (Eq.subst (motive := Nat.le (Nat.add n k)) (Nat.add_comm m k) (right k))

theorem sub_succ (n m : Nat) : Eq (Nat.sub n (succ m)) (pred (Nat.sub n m)) := Omega.rfl

protected theorem sub_zero (n : Nat) : Eq (Nat.sub n zero) n := Omega.rfl

protected theorem pred_zero : Eq (pred zero) zero := Omega.rfl

protected theorem pred_succ (n : Nat) : Eq (pred n.succ) n := Omega.rfl

theorem succ_ne_zero (n : Nat) : Not (Eq (succ n) zero) :=
  fun h => Eq.subst
    (motive := fun k => Nat.rec (motive := fun _ => Prop) False (fun _ _ => True) k) h True.intro

theorem eq_zero_of_add_eq_zero {n m : Nat} : Eq (Nat.add n m) zero →
    And (Eq n zero) (Eq m zero) := fun h =>
  (Nat.rec (motive := fun i => Eq (Nat.add n i) zero → And (Eq n zero) (Eq i zero))
    (fun ha => And.intro ha rfl)
    (fun i _ hn => False.elim (succ_ne_zero (Nat.add n i) hn)) m) h


/-- Subtracting the same allowance from a sum bound gives the remaining bound. -/
theorem sub_le_of_le_add {a b c : Nat} (h : Nat.le a (Nat.add c b)) : Nat.le (Nat.sub a b) c :=
  have zeroSub (n : Nat) : Eq (Nat.sub zero n) zero :=
    Nat.rec (motive := fun n => Eq (Nat.sub zero n) zero)
      rfl (fun _ ih => congrArg pred ih) n
  (Nat.rec (motive := fun n => ∀ value, Nat.le value (Nat.add c n) → Nat.le (Nat.sub value n) c)
    (fun _ bound => bound)
    (fun n ih value =>
      Nat.rec (motive := fun x => Nat.le x (Nat.add c (succ n)) → Nat.le (Nat.sub x (succ n)) c)
        (fun _ => Eq.subst (motive := fun x => Nat.le x c) (zeroSub (succ n)).symm (zero_le c))
        (fun x _ bound =>
          Eq.subst (motive := fun z => Nat.le z c) (succ_sub_succ_eq_sub x n).symm
            (ih x (le_of_succ_le_succ bound))) value)
    b) a h

end Omega.Nat
