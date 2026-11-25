module
prelude

public import OmegaMath.Arithmetic.Euclidean.Division

/-! Omega original.

Short-cut normal forms for a conjugacy equation in a length-graded free monoid.
The carrier, concatenation, length and power are parameters. Prefix splitting,
cancellation and the elementary power recurrences are the only word laws.
-/

@[expose] public section

namespace Omega.FreeMonoid.Conjugacy

open Omega Omega.Arithmetic

/-- Elementary laws for concatenation with length-directed prefix splitting. -/
structure Laws {W : Type u} (empty : W) (append : W → W → W)
    (length : W → Nat) (power : Nat → W → W) where
  assoc : ∀ a b c, Eq (append (append a b) c) (append a (append b c))
  empty_left : ∀ a, Eq (append empty a) a
  cancel_left : ∀ a b c, Eq (append a b) (append a c) → Eq b c
  length_append : ∀ a b, Eq (length (append a b)) ((length a).add (length b))
  power_zero : ∀ a, Eq (power Nat.zero a) empty
  power_succ : ∀ n a, Eq (power n.succ a) (append a (power n a))
  split : ∀ a b c d, Eq (append a b) (append c d) →
    Nat.le (length a) (length c) →
    Exists (fun r => And (Eq c (append a r)) (Eq b (append r d)))

variable {W : Type u} {empty : W} {append : W → W → W}
  {length : W → Nat} {power : Nat → W → W}

/-- A literal exponent and short prefix, together with its complementary suffix. -/
def Normal (append : W → W → W) (length : W → Nat) (power : Nat → W → W)
    (a b z : W) (n : Nat) (p q : W) : Prop :=
  And (Eq a (append p q)) (And (Eq b (append q p))
    (And (Eq z (append (power n a) p)) (Nat.lt (length p) (length a))))

private theorem expanded (L : Laws empty append length power) (n : Nat) (a p : W) :
    Eq (append (power n.succ a) p) (append a (append (power n a) p)) :=
  (congrArg (fun t => append t p) (L.power_succ n a)).trans (L.assoc a (power n a) p)

/-- Remove complete initial copies of the left word until the remaining prefix is short. -/
theorem exists_normal (L : Laws empty append length power) (a b z : W)
    (positive : Nat.lt Nat.zero (length a)) (equation : Eq (append a z) (append z b)) :
    Exists (fun n => Exists (fun p => Exists (fun q => Normal append length power a b z n p q))) :=
  (strongInduction (P := fun k => ∀ z, Eq (length z) k →
      Eq (append a z) (append z b) →
      Exists (fun n => Exists (fun p => Exists (fun q => Normal append length power a b z n p q))))
    (fun k ih z size equation =>
      (le_or_lt (length a) (length z)).elim
        (fun long => (L.split a z z b equation long).elim (fun r parts =>
          have shorter : Nat.lt (length r) k :=
            Eq.subst (motive := Nat.lt (length r)) size
              (Eq.subst (motive := Nat.lt (length r))
                ((congrArg length parts.left).trans (L.length_append a r)).symm
                (Eq.subst (motive := fun t => Nat.lt t ((length a).add (length r)))
                  (Nat.zero_add (length r)) (add_lt_add_right positive (length r))))
          have reduced : Eq (append a r) (append r b) := parts.left.symm.trans parts.right
          (ih (length r) shorter r rfl reduced).elim (fun n hn => hn.elim (fun p hp =>
            hp.elim (fun q normal =>
              Exists.intro n.succ (Exists.intro p (Exists.intro q
                (And.intro normal.left (And.intro normal.right.left
                  (And.intro
                    (parts.left.trans ((congrArg (append a) normal.right.right.left).trans
                      (expanded L n a p).symm)) normal.right.right.right))))))))))
        (fun short => (L.split z b a z equation.symm (le_of_lt short)).elim (fun q parts =>
          Exists.intro Nat.zero (Exists.intro z (Exists.intro q
            (And.intro parts.left (And.intro parts.right
              (And.intro
                ((congrArg (fun t => append t z) (L.power_zero a)).trans (L.empty_left z)).symm
                short)))))))) (length z)) z rfl equation

private theorem short_not_extended (L : Laws empty append length power) (a p t : W)
    (short : Nat.lt (length p) (length a)) : Not (Eq p (append a t)) :=
  fun same =>
    have lower : Nat.le (length a) (length p) :=
      Eq.subst (motive := Nat.le (length a))
        ((congrArg length same).trans (L.length_append a t)).symm
        (Eq.subst (motive := fun k => Nat.le k ((length a).add (length t)))
          (Nat.add_zero (length a))
          (Nat.add_le_add_left (Nat.zero_le (length t)) (length a)))
    lt_irrefl (length p) (lt_of_lt_of_le short lower)

/-- A fixed period has an injective exponent/short-remainder representation. -/
theorem power_short_unique (L : Laws empty append length power) (a : W)
    (n m : Nat) (p r : W) (hp : Nat.lt (length p) (length a))
    (hr : Nat.lt (length r) (length a))
    (same : Eq (append (power n a) p) (append (power m a) r)) :
    And (Eq n m) (Eq p r) :=
  (Nat.rec (motive := fun n => ∀ m p r,
      Nat.lt (length p) (length a) → Nat.lt (length r) (length a) →
      Eq (append (power n a) p) (append (power m a) r) → And (Eq n m) (Eq p r))
    (fun m => Nat.rec (motive := fun m => ∀ p r,
        Nat.lt (length p) (length a) → Nat.lt (length r) (length a) →
        Eq (append (power Nat.zero a) p) (append (power m a) r) →
        And (Eq Nat.zero m) (Eq p r))
      (fun p r _ _ same => And.intro rfl
        (((congrArg (fun t => append t p) (L.power_zero a)).trans (L.empty_left p)).symm.trans
          (same.trans ((congrArg (fun t => append t r) (L.power_zero a)).trans (L.empty_left r)))))
      (fun m _ p r hp _ same => False.elim (short_not_extended L a p (append (power m a) r) hp
        (((congrArg (fun t => append t p) (L.power_zero a)).trans (L.empty_left p)).symm.trans
          (same.trans (expanded L m a r))))) m)
    (fun n ih m => Nat.rec (motive := fun m => ∀ p r,
        Nat.lt (length p) (length a) → Nat.lt (length r) (length a) →
        Eq (append (power n.succ a) p) (append (power m a) r) →
        And (Eq n.succ m) (Eq p r))
      (fun p r _ hr same => False.elim (short_not_extended L a r (append (power n a) p) hr
        (((congrArg (fun t => append t r) (L.power_zero a)).trans (L.empty_left r)).symm.trans
          (same.symm.trans (expanded L n a p)))))
      (fun m _ p r hp hr same =>
        have reduced := L.cancel_left a (append (power n a) p) (append (power m a) r)
          ((expanded L n a p).symm.trans (same.trans (expanded L m a r)))
        have unique := ih m p r hp hr reduced
        And.intro (congrArg Nat.succ unique.left) unique.right) m) n) m p r hp hr same

/-- Every power followed by a cut prefix solves the corresponding conjugacy equation. -/
theorem normal_sound (L : Laws empty append length power) (a b z : W)
    (n : Nat) (p q : W) (normal : Normal append length power a b z n p q) :
    Eq (append a z) (append z b) :=
  have cut : Eq (append a p) (append p b) :=
    (congrArg (fun t => append t p) normal.left).trans
      ((L.assoc p q p).trans (congrArg (append p) normal.right.left.symm))
  have solve : ∀ n, Eq (append a (append (power n a) p)) (append (append (power n a) p) b) :=
    Nat.rec (motive := fun n =>
      Eq (append a (append (power n a) p)) (append (append (power n a) p) b))
      (have base := (congrArg (fun t => append t p) (L.power_zero a)).trans (L.empty_left p)
       (congrArg (append a) base).trans (cut.trans (congrArg (fun t => append t b) base.symm)))
      (fun n ih => (congrArg (append a) (expanded L n a p)).trans
        ((congrArg (append a) ih).trans
          ((L.assoc a (append (power n a) p) b).symm.trans
            (congrArg (fun t => append t b) (expanded L n a p).symm))))
  (congrArg (append a) normal.right.right.left).trans
    ((solve n).trans (congrArg (fun t => append t b) normal.right.right.left.symm))

/-- The complete normal form is unique, including exponent, prefix and suffix. -/
theorem normal_unique (L : Laws empty append length power) (a b z : W)
    (n m : Nat) (p q r s : W)
    (first : Normal append length power a b z n p q)
    (second : Normal append length power a b z m r s) :
    And (Eq n m) (And (Eq p r) (Eq q s)) :=
  have unique := power_short_unique L a n m p r first.right.right.right second.right.right.right
    (first.right.right.left.symm.trans second.right.right.left)
  And.intro unique.left (And.intro unique.right
    (L.cancel_left p q s
      (first.left.symm.trans (second.left.trans
        (congrArg (fun t => append t s) unique.right.symm)))))

end Omega.FreeMonoid.Conjugacy
