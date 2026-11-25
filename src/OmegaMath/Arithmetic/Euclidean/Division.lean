module
prelude
public import OmegaMath.Data.Nat

/-! Omega original.

Constructive natural order, divisibility, and Euclidean division.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

open Omega

/-- Equality of natural numbers as a strict Boolean. -/
def natEq (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (fun b => Nat.rec Bool.true (fun _ _ => Bool.false) b)
    (fun _ ih b => Nat.rec Bool.false (fun b _ => ih b) b) a b

theorem natEq_cases (a b : Nat) (P : Bool → Prop)
    (same : Eq a b → P Bool.true) (different : Not (Eq a b) → P Bool.false) :
    P (natEq a b) :=
  (Nat.rec (motive := fun a => ∀ b (P : Bool → Prop),
    (Eq a b → P Bool.true) → (Not (Eq a b) → P Bool.false) → P (natEq a b))
    (fun b => Nat.rec (motive := fun b => ∀ (P : Bool → Prop),
      (Eq Nat.zero b → P Bool.true) → (Not (Eq Nat.zero b) → P Bool.false) → P (natEq Nat.zero b))
      (fun _ same _ => same Eq.refl)
      (fun b _ _ _ different => different (fun h => Nat.succ_ne_zero b h.symm)) b)
    (fun a ih b => Nat.rec (motive := fun b => ∀ (P : Bool → Prop),
      (Eq a.succ b → P Bool.true) → (Not (Eq a.succ b) → P Bool.false) → P (natEq a.succ b))
      (fun _ _ different => different (Nat.succ_ne_zero a))
      (fun b _ P same different => ih b P
        (fun h => same (congrArg Nat.succ h)) (fun h => different (fun e => h (Nat.succ.inj e)))) b)
    a) b P same different

theorem le_or_lt (a b : Nat) : Or (Nat.le a b) (Nat.lt b a) :=
  (Nat.rec (motive := fun x => ∀ y, Or (Nat.le x y) (Nat.lt y x))
    (fun b => Or.inl (Nat.zero_le b))
    (fun a ih b => Nat.rec (motive := fun y => Or (Nat.le a.succ y) (Nat.lt y a.succ))
      (Or.inr (Nat.zero_le a)) (fun b _ =>
        (ih b).elim (fun h => Or.inl (Nat.succ_le_succ h))
          (fun h => Or.inr (Nat.succ_le_succ h))) b) a) b

theorem pos_of_ne_zero {n : Nat} (h : Not (Eq n Nat.zero)) : Nat.lt Nat.zero n :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → Nat.lt Nat.zero n)
    (fun h => False.elim (h Eq.refl)) (fun n _ _ => Nat.zero_le n) n) h

theorem le_of_lt {a b : Nat} (h : Nat.lt a b) : Nat.le a b :=
  Nat.le_trans (Nat.le.step (Nat.le.refl a)) h

theorem lt_of_le_of_lt {a b c : Nat} (h : Nat.le a b) (g : Nat.lt b c) : Nat.lt a c :=
  Nat.le_trans (Nat.succ_le_succ h) g

theorem lt_of_lt_of_le {a b c : Nat} (h : Nat.lt a b) (g : Nat.le b c) : Nat.lt a c :=
  Nat.le_trans h g

theorem lt_irrefl (a : Nat) : Not (Nat.lt a a) :=
  Nat.rec (motive := fun n => Not (Nat.lt n n)) (fun h => h) (fun _ ih h => ih h) a

theorem ne_of_lt {a b : Nat} (h : Nat.lt a b) : Not (Eq a b) :=
  fun e => lt_irrefl a (Eq.subst (Nat.lt a) e.symm h)

theorem lt_of_le_of_ne {a b : Nat} (h : Nat.le a b) (hne : Not (Eq a b)) : Nat.lt a b :=
  (le_or_lt b a).elim (fun g => False.elim (hne (Nat.le_antisymm h g))) (fun g => g)

theorem add_le_add_right {a b : Nat} (h : Nat.le a b) (c : Nat) :
    Nat.le (a.add c) (b.add c) :=
  Eq.subst (fun x => Nat.le x (b.add c)) (Nat.add_comm c a)
    (Eq.subst (Nat.le (c.add a)) (Nat.add_comm c b) (Nat.add_le_add_left h c))

theorem add_le_add {a b c d : Nat} (h : Nat.le a b) (g : Nat.le c d) :
    Nat.le (a.add c) (b.add d) :=
  Nat.le_trans (add_le_add_right h c) (Nat.add_le_add_left g b)

theorem add_lt_add_right {a b : Nat} (h : Nat.lt a b) (c : Nat) :
    Nat.lt (a.add c) (b.add c) :=
  Eq.subst (fun x => Nat.le x (b.add c)) (Nat.succ_add a c) (add_le_add_right h c)

theorem add_lt_add_left {a b : Nat} (h : Nat.lt a b) (c : Nat) :
    Nat.lt (c.add a) (c.add b) :=
  Nat.add_le_add_left h c

theorem mul_le_mul_right {a b : Nat} (h : Nat.le a b) (c : Nat) :
    Nat.le (a.mul c) (b.mul c) :=
  Nat.rec (motive := fun c => Nat.le (a.mul c) (b.mul c)) True.intro
    (fun _ ih => add_le_add ih h) c

theorem mul_le_mul_left {a b : Nat} (h : Nat.le a b) (c : Nat) :
    Nat.le (c.mul a) (c.mul b) :=
  Eq.subst (fun x => Nat.le x (c.mul b)) (Nat.mul_comm a c)
    (Eq.subst (Nat.le (a.mul c)) (Nat.mul_comm b c) (mul_le_mul_right h c))

theorem mul_pos {a b : Nat} (ha : Nat.lt Nat.zero a) (hb : Nat.lt Nat.zero b) :
    Nat.lt Nat.zero (a.mul b) :=
  Nat.le_trans ha (Eq.subst (fun x => Nat.le x (a.mul b)) (Nat.mul_one a) (mul_le_mul_left hb a))

/-- Strong induction using only the natural recursor. -/
theorem strongInduction {P : Nat → Prop}
    (step : ∀ n, (∀ m, Nat.lt m n → P m) → P n) (n : Nat) : P n :=
  step n (fun m => Nat.rec (motive := fun n => ∀ m, Nat.lt m n → P m)
    (fun _ h => False.elim h)
    (fun n ih m h => (le_or_lt n m).elim
      (fun g => Eq.subst P (Nat.le_antisymm g h) (step n ih)) (ih m)) n m)

def Dvd (a b : Nat) : Prop := Exists (fun k : Nat => Eq b (a.mul k))

theorem dvd_refl (a : Nat) : Dvd a a :=
  Exists.intro Nat.one (Nat.mul_one a).symm

theorem dvd_zero (a : Nat) : Dvd a Nat.zero := Exists.intro Nat.zero Eq.refl

theorem dvd_trans {a b c : Nat} (hab : Dvd a b) (hbc : Dvd b c) : Dvd a c :=
  hab.elim (fun x hx => hbc.elim (fun y hy =>
    Exists.intro (x.mul y) (hy.trans ((congrArg (fun t : Nat => t.mul y) hx).trans
      (Nat.mul_assoc a x y)))))

theorem le_of_dvd_of_pos {a b : Nat} (hab : Dvd a b) (hb : Nat.lt Nat.zero b) : Nat.le a b :=
  hab.elim (fun k hk =>
    have hn : Not (Eq k Nat.zero) := fun e =>
      ne_of_lt hb (hk.trans (congrArg (Nat.mul a) e)).symm
    Eq.subst (Nat.le a) hk.symm
      (Eq.subst (fun x => Nat.le x (a.mul k)) (Nat.mul_one a)
        (mul_le_mul_left (pos_of_ne_zero hn) a)))

theorem dvd_one {d : Nat} (h : Dvd d Nat.one) : Eq d Nat.one :=
  have hle := le_of_dvd_of_pos h (Nat.le.refl Nat.one)
  have hne : Not (Eq d Nat.zero) := fun e =>
    h.elim (fun k hk => Nat.succ_ne_zero Nat.zero (hk.trans
      ((congrArg (fun x : Nat => x.mul k) e).trans (Nat.zero_mul k))))
  Nat.le_antisymm hle (pos_of_ne_zero hne)

/-- Finite lists of natural numbers in the strict prelude. -/
inductive NatList where
  | nil
  | cons (head : Nat) (tail : NatList)

namespace NatList

def prod (s : NatList) : Nat :=
  NatList.rec Nat.one (fun head _ tailProduct => head.mul tailProduct) s

def Mem (p : Nat) (s : NatList) : Prop :=
  NatList.rec False (fun head _ tailMem => Or (Eq p head) tailMem) s

end NatList

structure DivMod where
  quotient : Nat
  remainder : Nat

def DivMod.step (d : Nat) (s : DivMod) : DivMod :=
  Bool.rec (DivMod.mk s.quotient s.remainder.succ) (DivMod.mk s.quotient.succ Nat.zero)
    (natEq s.remainder.succ d)

/-- Count units into the remainder, rolling it over at the divisor. -/
def divMod (n d : Nat) : DivMod :=
  Nat.rec (DivMod.mk Nat.zero Nat.zero) (fun _ s => DivMod.step d s) n

private theorem divModStep_spec (n d : Nat) (s : DivMod)
    (heq : Eq n ((d.mul s.quotient).add s.remainder))
    (hr : Nat.lt s.remainder d) :
    And (Eq n.succ ((d.mul (DivMod.step d s).quotient).add (DivMod.step d s).remainder))
      (Nat.lt (DivMod.step d s).remainder d) :=
  natEq_cases s.remainder.succ d (fun t =>
    let next := Bool.rec (motive := fun _ => DivMod) (DivMod.mk s.quotient s.remainder.succ) (DivMod.mk s.quotient.succ Nat.zero) t
    And (Eq n.succ ((d.mul next.quotient).add next.remainder)) (Nat.lt next.remainder d))
    (fun e => And.intro
      (show Eq n.succ ((d.mul s.quotient).add d) from
        (congrArg Nat.succ heq).trans (congrArg (Nat.add (d.mul s.quotient)) e))
      (Nat.le_trans (pos_of_ne_zero (Nat.succ_ne_zero s.remainder)) hr))
    (fun ne => And.intro
      (show Eq n.succ ((d.mul s.quotient).add s.remainder.succ) from congrArg Nat.succ heq)
      (lt_of_le_of_ne hr ne))


theorem divMod_spec (n d : Nat) (hd : Nat.lt Nat.zero d) :
    And (Eq n ((d.mul (divMod n d).quotient).add (divMod n d).remainder))
      (Nat.lt (divMod n d).remainder d) :=
  Nat.rec (motive := fun n =>
    And (Eq n ((d.mul (divMod n d).quotient).add (divMod n d).remainder))
      (Nat.lt (divMod n d).remainder d))
    (And.intro Eq.refl hd)
    (fun n ih => divModStep_spec n d (divMod n d) ih.left ih.right) n

/-- Two representations with remainders below the divisor have the same remainder. -/
theorem divMod_remainder_unique {d q r q' r' : Nat}
    (h : Eq ((d.mul q).add r) ((d.mul q').add r'))
    (hr : Nat.lt r d) (hr' : Nat.lt r' d) : Eq r r' :=
  let incompatible := fun (q r q' r' : Nat)
      (h : Eq ((d.mul q).add r) ((d.mul q').add r'))
      (hr : Nat.lt r d) (hlt : Nat.lt q q') =>
    have first : Nat.lt ((d.mul q).add r) (d.mul q.succ) := add_lt_add_left hr (d.mul q)
    have second := Nat.le_trans (mul_le_mul_left hlt d)
      (Nat.le_trans (Nat.le.refl (d.mul q')) (Nat.add_le_add_left (Nat.zero_le r') (d.mul q')))
    lt_irrefl _ (Eq.subst (fun n => Nat.lt ((d.mul q).add r) n) h.symm (lt_of_lt_of_le first second))
  (le_or_lt q q').elim
    (fun l => (le_or_lt q' q).elim
      (fun l' => Nat.add_left_cancel (Eq.subst
        (fun t => Eq ((d.mul q).add r) ((d.mul t).add r')) (Nat.le_antisymm l l').symm h))
      (fun g => False.elim (incompatible q r q' r' h hr g)))
    (fun g => False.elim (incompatible q' r' q r h.symm hr' g))

theorem dvd_iff_remainder_zero (n d : Nat) (hd : Nat.lt Nat.zero d) :
    Iff (Dvd d n) (Eq (divMod n d).remainder Nat.zero) :=
  let spec := divMod_spec n d hd
  Iff.intro
    (fun h => h.elim (fun k hk => divMod_remainder_unique (q' := k) (spec.left.symm.trans hk) spec.right hd))
    (fun e => Exists.intro (divMod n d).quotient
      (spec.left.trans (congrArg (Nat.add (d.mul (divMod n d).quotient)) e)))

end Omega.Arithmetic
