module
prelude
public import OmegaMath.Data.Nat

/-!
Omega original.

Exact division by a positive Peano natural.
-/

noncomputable section

@[expose] public section

namespace Omega.Fractran

open Omega

inductive Result where
  | none
  | some (state : Nat)

namespace Result

theorem some_inj {a b : Nat} (h : Eq (some a) (some b)) : Eq a b :=
  congrArg (Result.rec (motive := fun _ => Nat) Nat.zero (fun n => n)) h

theorem none_ne_some (n : Nat) : Not (Eq none (some n)) :=
  fun h => Eq.subst (Result.rec (motive := fun _ => Prop) True (fun _ => False)) h True.intro

end Result

structure Division where
  quotient : Nat
  remainder : Nat
  untilCarry : Nat

def advanceDivision (d : Nat) (s : Division) : Division :=
  Nat.rec ⟨s.quotient.succ, Nat.zero, d⟩ (fun c _ => ⟨s.quotient, s.remainder.succ, c⟩)
    s.untilCarry

def divide (d n : Nat) : Division :=
  Nat.rec ⟨Nat.zero, Nat.zero, d⟩ (fun _ => advanceDivision d) n

private def advanceBy (d k : Nat) (s : Division) : Division :=
  Nat.rec (fun s => s) (fun _ run s => run (advanceDivision d s)) k s

private theorem advanceBy_succ_last (d k : Nat) (s : Division) :
    Eq (advanceBy d k.succ s) (advanceDivision d (advanceBy d k s)) :=
  Nat.rec (motive := fun k => ∀ s, Eq (advanceBy d k.succ s) (advanceDivision d (advanceBy d k s)))
    (fun _ => Eq.refl) (fun _ ih s => ih (advanceDivision d s)) k s

private theorem divide_add (d n k : Nat) :
    Eq (divide d (n.add k)) (advanceBy d k (divide d n)) :=
  Nat.rec (motive := fun k => Eq (divide d (n.add k)) (advanceBy d k (divide d n)))
    Eq.refl (fun k ih => (congrArg (advanceDivision d) ih).trans (advanceBy_succ_last d k (divide d n)).symm)
    k

private theorem advance_until_carry (d q r c : Nat) :
    Eq (advanceBy d c ⟨q, r, c⟩) ⟨q, r.add c, Nat.zero⟩ :=
  Nat.rec (motive := fun c => ∀ r, Eq (advanceBy d c ⟨q, r, c⟩) ⟨q, r.add c, Nat.zero⟩)
    (fun _ => Eq.refl) (fun c ih r => (ih r.succ).trans
      (congrArg (fun x => Division.mk q x Nat.zero) (Nat.succ_add r c))) c r

private theorem divide_mul (d q : Nat) :
    Eq (divide d (d.succ.mul q)) ⟨q, Nat.zero, d⟩ :=
  Nat.rec (motive := fun q => Eq (divide d (d.succ.mul q)) ⟨q, Nat.zero, d⟩) Eq.refl
    (fun q ih => (divide_add d (d.succ.mul q) d.succ).trans
      ((congrArg (advanceBy d d.succ) ih).trans
        ((advanceBy_succ_last d d ⟨q, Nat.zero, d⟩).trans
          (congrArg (advanceDivision d)
            ((advance_until_carry d q Nat.zero d).trans
              (congrArg (fun r => Division.mk q r Nat.zero) (Nat.zero_add d))))))) q

private def DigitInvariant (d n : Nat) (s : Division) : Prop :=
  And (Eq (s.remainder.add s.untilCarry) d) (Eq ((d.succ.mul s.quotient).add s.remainder) n)

private theorem advance_invariant (d n : Nat) (s : Division) :
    DigitInvariant d n s → DigitInvariant d n.succ (advanceDivision d s) :=
  Division.rec (motive := fun s => DigitInvariant d n s → DigitInvariant d n.succ (advanceDivision d s))
    (fun q r c =>
      Nat.rec (motive := fun c => DigitInvariant d n ⟨q, r, c⟩ →
          DigitInvariant d n.succ (advanceDivision d ⟨q, r, c⟩))
        (fun h => And.intro (Nat.zero_add d)
          (congrArg Nat.succ ((congrArg (d.succ.mul q).add h.left.symm).trans h.right)))
        (fun c _ h => And.intro ((Nat.succ_add r c).trans h.left) (congrArg Nat.succ h.right)) c) s

private theorem divide_invariant (d n : Nat) : DigitInvariant d n (divide d n) :=
  Nat.rec (motive := fun n => DigitInvariant d n (divide d n))
    (And.intro (Nat.zero_add d) Eq.refl) (fun n => advance_invariant d n (divide d n)) n

def select (s : Division) : Result :=
  Nat.rec (.some s.quotient) (fun _ _ => .none) s.remainder

/-- Return the quotient exactly when division by the successor of d is exact. -/
def exactQuotient (n d : Nat) : Result := select (divide d n)

theorem exactQuotient_mul (d q : Nat) : Eq (exactQuotient (d.succ.mul q) d) (.some q) :=
  congrArg select (divide_mul d q)

private theorem select_sound (d n q : Nat) (s : Division) :
    Eq ((d.succ.mul s.quotient).add s.remainder) n →
    Eq (select s) (.some q) → Eq (d.succ.mul q) n :=
  Division.rec (motive := fun s => Eq ((d.succ.mul s.quotient).add s.remainder) n →
      Eq (select s) (.some q) → Eq (d.succ.mul q) n)
    (fun t r c => Nat.rec (motive := fun r => Eq ((d.succ.mul t).add r) n →
        Eq (select ⟨t, r, c⟩) (.some q) → Eq (d.succ.mul q) n)
      (fun hn hq => (congrArg d.succ.mul (Result.some_inj hq).symm).trans hn)
      (fun _ _ _ h => False.elim (Result.none_ne_some q h)) r) s

theorem exactQuotient_spec (n d q : Nat) :
    Iff (Eq (exactQuotient n d) (.some q)) (Eq (d.succ.mul q) n) :=
  Iff.intro (select_sound d n q (divide d n) (divide_invariant d n).right)
    (fun h => (congrArg (fun n => exactQuotient n d) h.symm).trans (exactQuotient_mul d q))

end Omega.Fractran
