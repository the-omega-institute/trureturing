module
prelude
public import OmegaMath.Arithmetic.Euclidean.Division

/-! Omega original.

Finite profile saturation. If every coordinate is bounded below and the
sum attains the sum of those bounds, every coordinate attains its bound.
This is the finite arithmetic step used to obtain simultaneous floor minima.
-/

@[expose] public section

namespace Omega.Arithmetic.SimultaneousFloor

open Omega

/-- Sum of the entries with indices strictly below `n`. -/
def sumBelow (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec Nat.zero (fun i s => s.add (f i)) n

theorem sumBelow_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, Nat.lt i n → Eq (f i) (g i)) :
    Eq (sumBelow n f) (sumBelow n g) :=
  (Nat.rec (motive := fun n => (∀ i, Nat.lt i n → Eq (f i) (g i)) →
      Eq (sumBelow n f) (sumBelow n g))
    (fun _ => rfl)
    (fun n ih h =>
      (congrArg (fun s => s.add (f n)) (ih (fun i hi => h i (Nat.le.step hi)))).trans
        (congrArg (Nat.add (sumBelow n g)) (h n (Nat.le_refl n.succ)))) n) h

theorem sumBelow_mono (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, Nat.lt i n → Nat.le (f i) (g i)) :
    Nat.le (sumBelow n f) (sumBelow n g) :=
  (Nat.rec (motive := fun n => (∀ i, Nat.lt i n → Nat.le (f i) (g i)) →
      Nat.le (sumBelow n f) (sumBelow n g))
    (fun _ => Nat.le_refl Nat.zero)
    (fun n ih h => add_le_add
      (ih (fun i hi => h i (Nat.le.step hi))) (h n (Nat.le_refl n.succ))) n) h

private theorem le_cancel_right (a b c : Nat) :
    Nat.le (a.add c) (b.add c) → Nat.le a b :=
  Nat.rec (motive := fun c => Nat.le (a.add c) (b.add c) → Nat.le a b)
    (fun h => h) (fun _ ih h => ih (Nat.le_of_succ_le_succ h)) c

private theorem add_saturation (a b c d : Nat)
    (hab : Nat.le a b) (hcd : Nat.le c d)
    (h : Eq (a.add c) (b.add d)) : And (Eq a b) (Eq c d) :=
  have hba : Nat.le b a := le_cancel_right b a c
    (Eq.subst (motive := Nat.le (b.add c)) h.symm (Nat.add_le_add_left hcd b))
  have e : Eq a b := Nat.le_antisymm hab hba
  And.intro e (Nat.add_left_cancel
    ((congrArg (fun x => x.add c) e).symm.trans h))

/-- Equality of finite sums with coordinatewise lower bounds is simultaneous equality. -/
theorem saturation (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, Nat.lt i n → Nat.le (f i) (g i))
    (hs : Eq (sumBelow n f) (sumBelow n g)) :
    ∀ i, Nat.lt i n → Eq (f i) (g i) :=
  (Nat.rec (motive := fun n =>
      (∀ i, Nat.lt i n → Nat.le (f i) (g i)) →
      Eq (sumBelow n f) (sumBelow n g) →
      ∀ i, Nat.lt i n → Eq (f i) (g i))
    (fun _ _ i hi => False.elim (Nat.not_succ_le_zero i hi))
    (fun n ih h hs =>
      let prior := fun i hi => h i (Nat.le.step hi)
      let split := add_saturation (sumBelow n f) (sumBelow n g) (f n) (g n)
        (sumBelow_mono n f g prior) (h n (Nat.le_refl n.succ)) hs
      fun i hi => (le_or_lt n i).elim
        (fun hni => Eq.subst (motive := fun i => Eq (f i) (g i))
          (Nat.le_antisymm (Nat.le_of_succ_le_succ hi) hni).symm split.right)
        (fun hin => ih prior split.left i hin)) n) h hs

end Omega.Arithmetic.SimultaneousFloor
