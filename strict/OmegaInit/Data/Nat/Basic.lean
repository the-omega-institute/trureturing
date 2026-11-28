/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Core
public import OmegaInit.SimpLemmas
public import OmegaInit.Data.NeZero

@[expose] public section

port_definition Nat.min with_native_code
port_definition Nat.instMax with_native_code
port_definition Nat.max with_native_code
port_proof Nat.min_def by_reflexivity
port_proof Nat.max_def by_reflexivity



namespace Omega.Nat


theorem beq_refl (a : Nat) : Eq (Nat.beq a a) Bool.true :=
  Nat.rec (motive := fun n => Eq (Nat.beq n n) Bool.true)
    Omega.rfl (fun _ ih => ih) a

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

theorem succ_eq_add_one (n : Nat) :
    Eq (succ n) (Nat.add n zero.succ) :=
  Omega.rfl

theorem add_one_ne_zero (n : Nat) :
    Ne (Nat.add n zero.succ) zero :=
  succ_ne_zero n

theorem zero_ne_add_one (n : Nat) :
    Ne zero (Nat.add n zero.succ) :=
  fun h => succ_ne_zero n h.symm

protected theorem add_left_comm (n m k : Nat) :
    Eq (Nat.add n (Nat.add m k)) (Nat.add m (Nat.add n k)) :=
  (Nat.add_assoc n m k).symm.trans
    ((congrArg (fun x => Nat.add x k) (Nat.add_comm n m)).trans (Nat.add_assoc m n k))

protected theorem eq_zero_of_add_eq_zero_left {n m : Nat} (h : Eq (Nat.add n m) zero) :
    Eq m zero :=
  (eq_zero_of_add_eq_zero h).right

theorem mul_add_one (n m : Nat) :
    Eq (Nat.mul n (Nat.add m zero.succ)) (Nat.add (Nat.mul n m) n) :=
  mul_succ n m

theorem add_one_mul (n m : Nat) :
    Eq (Nat.mul (Nat.add n zero.succ) m) (Nat.add (Nat.mul n m) m) :=
  succ_mul n m

protected theorem left_distrib (n m k : Nat) :
    Eq (Nat.mul n (Nat.add m k)) (Nat.add (Nat.mul n m) (Nat.mul n k)) :=
  Nat.mul_add n m k

protected theorem right_distrib (n m k : Nat) :
    Eq (Nat.mul (Nat.add n m) k) (Nat.add (Nat.mul n k) (Nat.mul m k)) :=
  Nat.add_mul n m k

protected theorem mul_left_comm (n m k : Nat) :
    Eq (Nat.mul n (Nat.mul m k)) (Nat.mul m (Nat.mul n k)) :=
  (Nat.mul_assoc n m k).symm.trans
    ((congrArg (fun x => Nat.mul x k) (Nat.mul_comm n m)).trans (Nat.mul_assoc m n k))

protected theorem mul_two (n : Nat) :
    Eq (Nat.mul n zero.succ.succ) (Nat.add n n) :=
  congrArg (fun x => Nat.add x n) (Nat.mul_one n)

protected theorem two_mul (n : Nat) :
    Eq (Nat.mul zero.succ.succ n) (Nat.add n n) :=
  (Nat.mul_comm zero.succ.succ n).trans (Nat.mul_two n)

theorem le_step {n m : Nat} (h : Nat.le n m) :
    Nat.le n (succ m) :=
  le.step h

theorem succ_lt_succ {n m : Nat} :
    Nat.lt n m → Nat.lt (succ n) (succ m) :=
  succ_le_succ

theorem le_of_lt_add_one {n m : Nat} :
    Nat.lt n (Nat.add m zero.succ) → Nat.le n m :=
  le_of_succ_le_succ

theorem lt_add_one_of_le {n m : Nat} :
    Nat.le n m → Nat.lt n (Nat.add m zero.succ) :=
  succ_le_succ

theorem not_add_one_le_zero (n : Nat) :
    Not (Nat.le (Nat.add n zero.succ) zero) :=
  not_succ_le_zero n

theorem succ_sub_succ (n m : Nat) :
    Eq (Nat.sub (succ n) (succ m)) (Nat.sub n m) :=
  succ_sub_succ_eq_sub n m

protected theorem sub_self (n : Nat) :
    Eq (Nat.sub n n) zero :=
  Nat.rec (motive := fun k => Eq (Nat.sub k k) zero) Omega.rfl
    (fun k ih => (succ_sub_succ k k).trans ih) n

theorem sub_add_eq (a b c : Nat) :
    Eq (Nat.sub a (Nat.add b c)) (Nat.sub (Nat.sub a b) c) :=
  Nat.rec (motive := fun k => Eq (Nat.sub a (Nat.add b k)) (Nat.sub (Nat.sub a b) k))
    Omega.rfl (fun _ ih => congrArg pred ih) c

protected theorem sub_sub (n m k : Nat) :
    Eq (Nat.sub (Nat.sub n m) k) (Nat.sub n (Nat.add m k)) :=
  (sub_add_eq n m k).symm

protected theorem zero_sub (n : Nat) :
    Eq (Nat.sub zero n) zero :=
  Nat.rec (motive := fun k => Eq (Nat.sub zero k) zero)
    Omega.rfl (fun _ ih => congrArg pred ih) n

protected theorem zero_sub_one :
    Eq (Nat.sub zero zero.succ) zero :=
  Omega.rfl

protected theorem add_one_sub_one (n : Nat) :
    Eq (Nat.sub (Nat.add n zero.succ) zero.succ) n :=
  Omega.rfl

theorem le_add_right (n k : Nat) :
    Nat.le n (Nat.add n k) :=
  Nat.rec (motive := fun k => Nat.le n (Nat.add n k)) (Nat.le_refl n)
    (fun _ ih => le.step ih) k

theorem le_add_left (n m : Nat) :
    Nat.le n (Nat.add m n) :=
  Eq.subst (motive := Nat.le n) (Nat.add_comm n m) (le_add_right n m)

theorem le_of_add_right_le {n m k : Nat} (h : Nat.le (Nat.add n k) m) :
    Nat.le n m :=
  Nat.le_trans (le_add_right n k) h

theorem le_add_right_of_le {n m k : Nat} (h : Nat.le n m) :
    Nat.le n (Nat.add m k) :=
  Nat.le_trans h (le_add_right m k)

theorem le_of_add_left_le {n m k : Nat} (h : Nat.le (Nat.add k n) m) :
    Nat.le n m :=
  Nat.le_trans (le_add_left n k) h

theorem le_add_left_of_le {n m k : Nat} (h : Nat.le n m) :
    Nat.le n (Nat.add k m) :=
  Nat.le_trans h (le_add_left m k)

theorem lt_of_add_one_le {n m : Nat} (h : Nat.le (Nat.add n zero.succ) m) :
    Nat.lt n m :=
  h

theorem add_one_le_of_lt {n m : Nat} (h : Nat.lt n m) :
    Nat.le (Nat.add n zero.succ) m :=
  h

protected theorem lt_succ_iff {m n : Nat} :
    Iff (Nat.lt m (succ n)) (Nat.le m n) :=
  Iff.intro le_of_succ_le_succ succ_le_succ

protected theorem lt_add_one_iff {m n : Nat} :
    Iff (Nat.lt m (Nat.add n zero.succ)) (Nat.le m n) :=
  Nat.lt_succ_iff

theorem lt_succ {m n : Nat} :
    Iff (Nat.lt m (succ n)) (Nat.le m n) :=
  Nat.lt_succ_iff

theorem lt_succ_of_lt {a b : Nat} (h : Nat.lt a b) :
    Nat.lt a (succ b) :=
  le.step h

theorem lt.step {n m : Nat} :
    Nat.lt n m → Nat.lt n (succ m) :=
  le.step

theorem lt_add_one_of_lt {a b : Nat} (h : Nat.lt a b) :
    Nat.lt a (Nat.add b zero.succ) :=
  le.step h

theorem succ_inj {a b : Nat} :
    Iff (Eq (succ a) (succ b)) (Eq a b) :=
  Iff.intro succ.inj (congrArg succ)

theorem succ_le_succ_iff {a b : Nat} :
    Iff (Nat.le (succ a) (succ b)) (Nat.le a b) :=
  Iff.intro le_of_succ_le_succ succ_le_succ

theorem succ_lt_succ_iff {a b : Nat} :
    Iff (Nat.lt (succ a) (succ b)) (Nat.lt a b) :=
  succ_le_succ_iff

theorem succ_ne_succ_iff {a b : Nat} :
    Iff (Ne (succ a) (succ b)) (Ne a b) :=
  Iff.intro (fun hn h => hn (congrArg succ h)) (fun hn h => hn (succ.inj h))

theorem add_one_inj {a b : Nat} :
    Iff (Eq (Nat.add a zero.succ) (Nat.add b zero.succ)) (Eq a b) :=
  succ_inj

theorem add_one_le_add_one_iff {a b : Nat} :
    Iff (Nat.le (Nat.add a zero.succ) (Nat.add b zero.succ)) (Nat.le a b) :=
  succ_le_succ_iff

theorem add_one_lt_add_one_iff {a b : Nat} :
    Iff (Nat.lt (Nat.add a zero.succ) (Nat.add b zero.succ)) (Nat.lt a b) :=
  succ_lt_succ_iff

theorem add_one_ne_add_one_iff {a b : Nat} :
    Iff (Ne (Nat.add a zero.succ) (Nat.add b zero.succ)) (Ne a b) :=
  succ_ne_succ_iff

theorem add_one_le_iff {n m : Nat} :
    Iff (Nat.le (Nat.add n zero.succ) m) (Nat.lt n m) :=
  Iff.rfl

protected theorem add_le_add_right {n m : Nat} (h : Nat.le n m) (k : Nat) :
    Nat.le (Nat.add n k) (Nat.add m k) :=
  Nat.rec (motive := fun k => Nat.le (Nat.add n k) (Nat.add m k)) h
    (fun _ ih => succ_le_succ ih) k

protected theorem le_of_add_le_add_right {a b c : Nat} :
    Nat.le (Nat.add a b) (Nat.add c b) → Nat.le a c :=
  Nat.rec (motive := fun b => Nat.le (Nat.add a b) (Nat.add c b) → Nat.le a c)
    id (fun _ ih bound => ih (le_of_succ_le_succ bound)) b

protected theorem le_of_add_le_add_left {a b c : Nat} (h : Nat.le (Nat.add a b) (Nat.add a c)) :
    Nat.le b c :=
  Nat.le_of_add_le_add_right
    (Eq.subst (motive := fun y => Nat.le (Nat.add b a) y) (Nat.add_comm a c)
      (Eq.subst (motive := fun x => Nat.le x (Nat.add a c)) (Nat.add_comm a b) h))

protected theorem add_le_add_iff_right {m k n : Nat} :
    Iff (Nat.le (Nat.add m n) (Nat.add k n)) (Nat.le m k) :=
  Iff.intro Nat.le_of_add_le_add_right (fun h => Nat.add_le_add_right h n)

protected theorem add_le_add_iff_left {m k n : Nat} :
    Iff (Nat.le (Nat.add n m) (Nat.add n k)) (Nat.le m k) :=
  Iff.intro Nat.le_of_add_le_add_left (fun h => Nat.add_le_add_left h n)

theorem add_le_add {a b c d : Nat} (h₁ : Nat.le a b) (h₂ : Nat.le c d) :
    Nat.le (Nat.add a c) (Nat.add b d) :=
  Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)

protected theorem add_sub_add_right (n k m : Nat) :
    Eq (Nat.sub (Nat.add n k) (Nat.add m k)) (Nat.sub n m) :=
  Nat.rec (motive := fun k => Eq (Nat.sub (Nat.add n k) (Nat.add m k)) (Nat.sub n m))
    Omega.rfl (fun k ih => (succ_sub_succ (Nat.add n k) (Nat.add m k)).trans ih) k

protected theorem add_sub_cancel (n m : Nat) :
    Eq (Nat.sub (Nat.add n m) m) n :=
  Nat.rec (motive := fun m => Eq (Nat.sub (Nat.add n m) m) n) Omega.rfl
    (fun m ih => (succ_sub_succ (Nat.add n m) m).trans ih) m

protected theorem add_sub_cancel_left (n m : Nat) :
    Eq (Nat.sub (Nat.add n m) n) m :=
  (congrArg (fun x => Nat.sub x n) (Nat.add_comm n m)).trans (Nat.add_sub_cancel m n)

theorem and_forall_add_one {p : Nat → Prop} :
    Iff (And (p zero) (∀ (n : Nat), p (Nat.add n zero.succ))) (∀ (n : Nat), p n) :=
  Iff.intro (fun h => Nat.rec (motive := p) h.left (fun n _ => h.right n))
    (fun h => And.intro (h zero) (fun n => h (succ n)))

theorem or_exists_add_one {p : Nat → Prop} :
    Iff (Or (p zero) (Exists fun n => p (Nat.add n zero.succ))) (Exists p) :=
  Iff.intro
    (fun h => h.elim (Exists.intro zero) (fun hs => hs.elim (fun n => Exists.intro (succ n))))
    (fun h => h.elim (Nat.rec (motive := fun n => p n → Or (p zero) (Exists (fun k => p (succ k))))
      Or.inl (fun n _ hn => Or.inr (Exists.intro n hn))))

theorem le_zero {i : Nat} :
    Iff (Nat.le i zero) (Eq i zero) :=
  Iff.intro (fun h => Nat.le_antisymm h (zero_le i)) (fun h => Eq.subst (motive := fun i => Nat.le i zero) h.symm (zero_le zero))

protected theorem zero_lt_one :
    Nat.lt zero zero.succ :=
  succ_le_succ (zero_le zero)

protected theorem two_pos :
    Nat.lt zero zero.succ.succ :=
  succ_le_succ (zero_le zero.succ)

protected theorem zero_lt_two :
    Nat.lt zero zero.succ.succ :=
  Nat.two_pos

protected theorem one_lt_two :
    Nat.lt zero.succ zero.succ.succ :=
  succ_lt_succ Nat.zero_lt_one

theorem succ_pred_eq_of_ne_zero {n : Nat} :
    Ne n zero → Eq (succ (pred n)) n :=
  Nat.rec (motive := fun n => Ne n zero → Eq (succ (pred n)) n)
    (fun h => False.elim (h Omega.rfl)) (fun _ _ _ => Omega.rfl) n

theorem eq_zero_or_eq_succ_pred (n : Nat) :
    Or (Eq n zero) (Eq n (succ (pred n))) :=
  Nat.rec (motive := fun n => Or (Eq n zero) (Eq n (succ (pred n))))
    (Or.inl Omega.rfl) (fun _ _ => Or.inr Omega.rfl) n

protected theorem add_sub_add_left (k n m : Nat) :
    Eq (Nat.sub (Nat.add k n) (Nat.add k m)) (Nat.sub n m) :=
  (congrArg (fun x => Nat.sub x (Nat.add k m)) (Nat.add_comm k n)).trans
    ((congrArg (Nat.sub (Nat.add n k)) (Nat.add_comm k m)).trans (Nat.add_sub_add_right n k m))

protected theorem sub_self_add (n m : Nat) :
    Eq (Nat.sub n (Nat.add n m)) zero :=
  (Nat.sub_add_eq n n m).trans ((congrArg (fun x => Nat.sub x m) (Nat.sub_self n)).trans (Nat.zero_sub m))

protected theorem pow_zero (n : Nat) :
    Eq (Nat.pow n zero) zero.succ :=
  Omega.rfl

protected theorem pow_succ (n m : Nat) :
    Eq (Nat.pow n (succ m)) (Nat.mul (Nat.pow n m) n) :=
  Omega.rfl

protected theorem pow_add_one (n m : Nat) :
    Eq (Nat.pow n (Nat.add m zero.succ)) (Nat.mul (Nat.pow n m) n) :=
  Nat.pow_succ n m

protected theorem pow_one (a : Nat) :
    Eq (Nat.pow a zero.succ) a :=
  Nat.one_mul a

protected theorem mul_pow (a b n : Nat) :
    Eq (Nat.pow (Nat.mul a b) n) (Nat.mul (Nat.pow a n) (Nat.pow b n)) :=
  Nat.rec (motive := fun k => Eq (Nat.pow (Nat.mul a b) k) (Nat.mul (Nat.pow a k) (Nat.pow b k)))
    (Nat.mul_one zero.succ).symm (fun k ih =>
      (congrArg (fun x => Nat.mul x (Nat.mul a b)) ih).trans
        ((Nat.mul_assoc (Nat.pow a k) (Nat.pow b k) (Nat.mul a b)).trans
          ((congrArg (Nat.mul (Nat.pow a k)) (Nat.mul_left_comm (Nat.pow b k) a b)).trans
            (Nat.mul_assoc (Nat.pow a k) a (Nat.mul (Nat.pow b k) b)).symm))) n

end Omega.Nat

namespace Omega.Nat

theorem le.dest {n m : Nat} : Nat.le n m → Exists (fun k => Eq (Nat.add n k) m) := fun h =>
  Nat.le.rec (motive := fun m _ => Exists (fun k => Eq (Nat.add n k) m))
    (Exists.intro zero Omega.rfl) (fun {_} _ ih => ih.elim (fun k e => Exists.intro (succ k) (congrArg succ e))) h

theorem le.intro {n m k : Nat} (h : Eq (Nat.add n k) m) : Nat.le n m :=
  Eq.subst (motive := Nat.le n) h (le_add_right n k)

protected theorem not_le_of_lt {a b : Nat} : Nat.lt a b → Not (Nat.le b a) :=
  fun h bound => Nat.lt_irrefl a (Nat.le_trans h bound)

protected theorem lt_of_not_ge {a b : Nat} : Not (Nat.le a b) → Nat.lt b a :=
  Nat.rec (motive := fun a => ∀ b, Not (Nat.le a b) → Nat.lt b a)
    (fun b h => False.elim (h (zero_le b)))
    (fun a ih b => Nat.casesOn (motive := fun b => Not (Nat.le (succ a) b) → Nat.lt b (succ a)) b
      (fun _ => succ_le_succ (zero_le a)) (fun b h => succ_le_succ (ih b (fun e => h (succ_le_succ e))))) a b

protected theorem not_le {a b : Nat} : Iff (Not (Nat.le a b)) (Nat.lt b a) :=
  Iff.intro Nat.lt_of_not_ge Nat.not_le_of_lt

theorem add_sub_self_left (a b : Nat) : Eq (Nat.sub (Nat.add a b) a) b := Nat.add_sub_cancel_left a b

theorem add_sub_of_le {a b : Nat} (h : Nat.le a b) : Eq (Nat.add a (Nat.sub b a)) b :=
  (le.dest h).elim (fun k e => Eq.subst (motive := fun x => Eq (Nat.add a (Nat.sub x a)) x) e
    (congrArg (Nat.add a) (Nat.add_sub_cancel_left a k)))

protected theorem sub_add_cancel {n m : Nat} (h : Nat.le m n) : Eq (Nat.add (Nat.sub n m) m) n :=
  (Nat.add_comm (Nat.sub n m) m).trans (add_sub_of_le h)

theorem le_sub_of_add_le {a b c : Nat} (h : Nat.le (Nat.add a b) c) : Nat.le a (Nat.sub c b) :=
  Nat.le_of_add_le_add_right (b := b) (Eq.subst (motive := Nat.le (Nat.add a b))
    (Nat.sub_add_cancel (Nat.le_trans (le_add_left b a) h)).symm h)

theorem zero_lt_sub_of_lt {i a : Nat} (h : Nat.lt i a) : Nat.lt zero (Nat.sub a i) :=
  (le.dest h).elim (fun k e => Eq.subst (motive := fun n => Nat.lt zero (Nat.sub n i)) e
    (Eq.subst (motive := Nat.lt zero)
      ((congrArg (fun n => Nat.sub n i) ((succ_add i k).trans (add_succ i k).symm)).trans
        (Nat.add_sub_cancel_left i (succ k))).symm (succ_le_succ (zero_le k))))

theorem pred_lt {n : Nat} : Ne n zero → Nat.lt (pred n) n :=
  Nat.casesOn (motive := fun n => Ne n zero → Nat.lt (pred n) n) n
    (fun h => False.elim (h Omega.rfl)) (fun k _ => Nat.le_refl (succ k))

theorem sub_succ_lt_self (a i : Nat) (h : Nat.lt i a) : Nat.lt (Nat.sub a (succ i)) (Nat.sub a i) :=
  pred_lt (fun e => Nat.lt_irrefl zero (Eq.subst (motive := Nat.lt zero) e (zero_lt_sub_of_lt h)))

theorem mul_le_mul_left {n m : Nat} (k : Nat) (h : Nat.le n m) : Nat.le (Nat.mul k n) (Nat.mul k m) :=
  (le.dest h).elim (fun d e => le.intro ((Nat.mul_add k n d).symm.trans (congrArg (Nat.mul k) e)))

theorem mul_le_mul_right {n m : Nat} (k : Nat) (h : Nat.le n m) : Nat.le (Nat.mul n k) (Nat.mul m k) :=
  Eq.subst (motive := fun z => Nat.le z (Nat.mul m k)) (Nat.mul_comm k n)
    (Eq.subst (motive := Nat.le (Nat.mul k n)) (Nat.mul_comm k m) (mul_le_mul_left k h))

protected theorem mul_le_mul {n₁ m₁ n₂ m₂ : Nat} (h₁ : Nat.le n₁ n₂) (h₂ : Nat.le m₁ m₂) :
    Nat.le (Nat.mul n₁ m₁) (Nat.mul n₂ m₂) :=
  Nat.le_trans (mul_le_mul_right m₁ h₁) (mul_le_mul_left n₂ h₂)

protected theorem mul_lt_mul_of_pos_left {n m k : Nat} (h : Nat.lt n m) (hk : Nat.lt zero k) :
    Nat.lt (Nat.mul k n) (Nat.mul k m) :=
  have grow : Nat.lt (Nat.mul k n) (Nat.mul k (succ n)) :=
    Eq.subst (motive := Nat.lt (Nat.mul k n)) (mul_succ k n).symm (Nat.add_le_add_left hk (Nat.mul k n))
  Nat.le_trans grow (mul_le_mul_left k h)

protected theorem mul_lt_mul_of_pos_right {n m k : Nat} (h : Nat.lt n m) (hk : Nat.lt zero k) :
    Nat.lt (Nat.mul n k) (Nat.mul m k) :=
  Eq.subst (motive := fun z => Nat.lt z (Nat.mul m k)) (Nat.mul_comm k n)
    (Eq.subst (motive := Nat.lt (Nat.mul k n)) (Nat.mul_comm k m) (Nat.mul_lt_mul_of_pos_left h hk))

protected theorem pow_le_pow_right {n : Nat} (hx : Nat.lt zero n) {i : Nat} :
    ∀ {j}, Nat.le i j → Nat.le (Nat.pow n i) (Nat.pow n j) := fun {_} h =>
  Nat.le.rec (motive := fun j _ => Nat.le (Nat.pow n i) (Nat.pow n j))
    (Nat.le_refl _) (fun {j} _ ih => Nat.le_trans ih
      (Eq.subst (motive := fun z => Nat.le z (Nat.pow n (succ j))) (Nat.mul_one (Nat.pow n j))
        (mul_le_mul_left (Nat.pow n j) hx))) h

protected theorem two_pow_pos (w : Nat) : Nat.lt zero (Nat.pow (succ (succ zero)) w) :=
  Nat.pow_le_pow_right (i := zero) Nat.zero_lt_two (zero_le w)

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (add_assoc add_comm add_le_add add_le_add_iff_left add_le_add_iff_right add_le_add_left add_le_add_right add_left_cancel add_left_comm add_mul add_one add_one_inj add_one_le_add_one_iff add_one_le_iff add_one_le_of_lt add_one_lt_add_one_iff add_one_mul add_one_ne_add_one_iff add_one_ne_zero add_one_sub_one add_right_cancel add_right_comm add_sub_add_left add_sub_add_right add_sub_cancel add_sub_cancel_left add_sub_of_le add_sub_self_left add_succ and_forall_add_one beq_refl eq_zero_of_add_eq_zero eq_zero_of_add_eq_zero_left eq_zero_or_eq_succ_pred le_add_left le_add_left_of_le le_add_right le_add_right_of_le le_of_add_le_add_left le_of_add_le_add_right le_of_add_left_le le_of_add_right_le le_of_lt_add_one le_step le_sub_of_add_le le_total le_zero left_distrib lt_add_one_iff lt_add_one_of_le lt_add_one_of_lt lt_of_add_one_le lt_of_not_ge lt_succ lt_succ_iff lt_succ_of_lt mul_add mul_add_one mul_assoc mul_comm mul_le_mul mul_le_mul_left mul_le_mul_right mul_left_comm mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right mul_one mul_pow mul_succ mul_two mul_zero not_add_one_le_zero not_le not_le_of_lt one_lt_two one_mul or_exists_add_one pow_add_one pow_le_pow_right pow_one pow_succ pow_zero pred_lt pred_succ pred_zero right_distrib sub_add_cancel sub_add_eq sub_le_of_le_add sub_self sub_self_add sub_sub sub_succ sub_succ_lt_self sub_zero succ_add succ_eq_add_one succ_inj succ_le_succ_iff succ_lt_succ succ_lt_succ_iff succ_mul succ_ne_succ_iff succ_ne_zero succ_pred_eq_of_ne_zero succ_sub_succ two_mul two_pos two_pow_pos zero_add zero_lt_one zero_lt_sub_of_lt zero_lt_two zero_mul zero_ne_add_one zero_sub zero_sub_one)
end Nat

port_definition Nat.recAux
port_proof Nat.ge_of_not_lt
port_proof Nat.not_le_of_gt
port_proof Nat.not_lt_of_ge
port_definition Nat.casesAuxOn
port_proof Nat.le_of_not_gt

public section
namespace Nat
export _root_.Omega.Nat (casesAuxOn ge_of_not_lt instMax le_of_not_gt max max_def min min_def not_le_of_gt not_lt_of_ge recAux)
end Nat

port_proof Nat.succ_le_of_lt
port_proof Nat.lt_of_succ_le
port_proof Nat.add_lt_add_left
port_proof Nat.add_lt_add_right
port_proof Nat.eq_zero_or_pos
port_proof Nat.instNeZeroSucc
attribute [instance] Omega.Nat.instNeZeroSucc Omega.Nat.instMax
port_proof Nat.le_of_succ_le
port_proof Nat.le_of_lt
port_proof Nat.ne_of_lt
port_proof Nat.ne_of_gt
port_proof Nat.pos_of_ne_zero
port_proof Nat.pos_iff_ne_zero
port_proof Nat.pos_of_neZero
port_definition Nat.sub_le_sub_right._f
port_proof Nat.sub_le_sub_right
port_proof Nat.succ_sub
port_proof Nat.sub_lt_left_of_lt_add
port_proof Nat.sub_lt_right_of_lt_add

public section
namespace Nat
export _root_.Omega.Nat (add_lt_add_left add_lt_add_right eq_zero_or_pos instNeZeroSucc le_of_lt le_of_succ_le lt_of_succ_le ne_of_gt ne_of_lt pos_iff_ne_zero pos_of_neZero pos_of_ne_zero sub_le_sub_right sub_lt_left_of_lt_add sub_lt_right_of_lt_add succ_le_of_lt succ_sub)
end Nat

port_proof Nat.not_lt
port_proof Nat.lt_of_succ_lt_succ
port_private_declaration Nat.sub_ne_zero_of_lt.match_1_1
port_definition Nat.sub_ne_zero_of_lt._f by_constructive_casts
port_proof Nat.sub_ne_zero_of_lt
port_proof Nat.sub_pos_of_lt
port_private_declaration Nat.sub_eq_zero_of_le.match_1_1
port_proof Nat.sub_eq_zero_of_le
port_proof Nat.pred_mul by_constructive_casts
port_proof Nat.mul_sub_right_distrib by_constructive_casts
port_private_declaration Nat.sub_le_sub_left.match_1_1
port_proof Nat.sub_le_sub_left
port_private_declaration Nat.succ_pred_eq_of_pos.match_1_1
port_proof Nat.succ_pred_eq_of_pos

public section
namespace Nat
export _root_.Omega.Nat (lt_of_succ_lt_succ mul_sub_right_distrib not_lt pred_mul sub_eq_zero_of_le sub_le_sub_left sub_ne_zero_of_lt sub_pos_of_lt succ_pred_eq_of_pos)
end Nat

port_proof Nat.mul_sub_left_distrib
port_proof Nat.le_of_eq
port_proof Nat.le_of_mul_le_mul_left
port_proof Nat.eq_of_mul_eq_mul_left
port_private_declaration Nat.sub_eq_iff_eq_add.match_1_1
port_proof Nat.sub_eq_iff_eq_add
port_proof Nat.le_of_not_le
port_proof Nat.mul_sub

public section
namespace Nat
export _root_.Omega.Nat (eq_of_mul_eq_mul_left le_of_eq le_of_mul_le_mul_left le_of_not_le mul_sub mul_sub_left_distrib sub_eq_iff_eq_add)
end Nat

port_proof Nat.succ_ne_self
port_proof Nat.zero_ne_one

public section
namespace Nat
export _root_.Omega.Nat (succ_ne_self zero_ne_one)
end Nat

port_proof Nat.eq_of_mul_eq_mul_right by_constructive_casts

namespace Nat
export _root_.Omega.Nat (eq_of_mul_eq_mul_right)
end Nat
