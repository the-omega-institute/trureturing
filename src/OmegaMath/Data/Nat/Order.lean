module
prelude
import all OmegaInit.Prelude
public import OmegaInit.Data.Nat.Lemmas

/-! Omega original.

Constructive natural order and strong induction.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

open Omega

theorem le_or_lt (a b : Nat) : Or (Nat.le a b) (Nat.lt b a) :=
  (Nat.rec (motive := fun x => ∀ y, Or (Nat.le x y) (Nat.lt y x))
    (fun b => Or.inl (Nat.zero_le b))
    (fun a ih b => Nat.rec (motive := fun y => Or (Nat.le a.succ y) (Nat.lt y a.succ))
      (Or.inr (Nat.succ_le_succ (Nat.zero_le a))) (fun b _ =>
        (ih b).elim (fun h => Or.inl (Nat.succ_le_succ h))
          (fun h => Or.inr (Nat.succ_le_succ h))) b) a) b

theorem le_of_lt {a b : Nat} (h : Nat.lt a b) : Nat.le a b :=
  Nat.le_trans (Nat.le.step (Nat.le_refl a)) h

theorem lt_of_lt_of_le {a b c : Nat} (h : Nat.lt a b) (g : Nat.le b c) : Nat.lt a c :=
  Nat.le_trans h g

theorem lt_irrefl (a : Nat) : Not (Nat.lt a a) :=
  Nat.rec (motive := fun n => Not (Nat.lt n n)) (Nat.not_succ_le_zero Nat.zero) (fun _ ih h => ih (Nat.le_of_succ_le_succ h)) a

theorem add_le_add_right {a b : Nat} (h : Nat.le a b) (c : Nat) :
    Nat.le (a.add c) (b.add c) :=
  Eq.subst (motive := fun x => Nat.le x (b.add c)) (Nat.add_comm c a)
    (Eq.subst (motive := Nat.le (c.add a)) (Nat.add_comm c b) (Nat.add_le_add_left h c))

theorem add_lt_add_right {a b : Nat} (h : Nat.lt a b) (c : Nat) :
    Nat.lt (a.add c) (b.add c) :=
  Eq.subst (motive := fun x => Nat.le x (b.add c)) (Nat.succ_add a c) (add_le_add_right h c)

/-- Strong induction using only the natural recursor. -/
theorem strongInduction {P : Nat → Prop}
    (step : ∀ n, (∀ m, Nat.lt m n → P m) → P n) (n : Nat) : P n :=
  step n (fun m => Nat.rec (motive := fun n => ∀ m, Nat.lt m n → P m)
    (fun m h => False.elim (Nat.not_succ_le_zero m h))
    (fun n ih m h => (le_or_lt n m).elim
      (fun g => Eq.subst (motive := P) (Nat.le_antisymm g (Nat.le_of_succ_le_succ h)) (step n ih)) (ih m)) n m)

end Omega.Arithmetic
