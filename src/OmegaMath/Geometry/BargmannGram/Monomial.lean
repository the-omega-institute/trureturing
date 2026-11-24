module
prelude
public import OmegaMath.Data.Int

/-!
Omega original.

Products of indexed variables for integer polynomial equality certificates.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram.Polynomial

inductive Ordering where
  | less
  | equal
  | greater

def compareIndex (i j : Nat) : Ordering :=
  (Nat.rec (motive := fun _ => Nat → Ordering)
    (fun j => Nat.rec .equal (fun _ _ => .less) j)
    (fun _ cmp j => Nat.rec .greater (fun k _ => cmp k) j) i) j

theorem compareIndex_eq (i j : Nat) : Eq (compareIndex i j) .equal → Eq i j :=
  (Nat.rec (motive := fun i => ∀ j, Eq (compareIndex i j) .equal → Eq i j)
    (fun j => Nat.rec (motive := fun j => Eq (compareIndex Nat.zero j) .equal → Eq Nat.zero j)
      (fun _ => Eq.refl)
      (fun _ _ h => False.elim (Eq.subst (Ordering.rec (motive := fun _ => Prop) True False True) h True.intro)) j)
    (fun i ih j => Nat.rec (motive := fun j => Eq (compareIndex i.succ j) .equal → Eq i.succ j)
      (fun h => False.elim (Eq.subst (Ordering.rec (motive := fun _ => Prop) True False True) h True.intro))
      (fun k _ h => congrArg Nat.succ (ih k h)) j) i) j

inductive Monomial where
  | one
  | factor (index : Nat) (tail : Monomial)

namespace Monomial

def eval (v : Nat → Int) (m : Monomial) : Int :=
  Monomial.rec Int.one (fun i _ r => (v i).mul r) m

def insert (i : Nat) (m : Monomial) : Monomial :=
  Monomial.rec (.factor i .one)
    (fun j m r => Ordering.rec (.factor i (.factor j m)) (.factor i (.factor j m))
      (.factor j r) (compareIndex i j)) m

private theorem eval_insert (v : Nat → Int) (i : Nat) (m : Monomial) :
    Eq (eval v (insert i m)) ((v i).mul (eval v m)) :=
  Monomial.rec (motive := fun m => Eq (eval v (insert i m)) ((v i).mul (eval v m)))
    Eq.refl
    (fun j m ih =>
      let insertHere := Monomial.factor i (.factor j m)
      let insertLater := Monomial.factor j (insert i m)
      Ordering.rec (motive := fun o =>
        Eq (eval v (Ordering.rec (motive := fun _ => Monomial) insertHere insertHere insertLater o))
          ((v i).mul (eval v (.factor j m))))
        Eq.refl Eq.refl
        ((congrArg (v j).mul ih).trans
          ((Int.mul_assoc (v j) (v i) (eval v m)).symm.trans
            ((congrArg (fun a : Int => a.mul (eval v m)) (Int.mul_comm (v j) (v i))).trans
              (Int.mul_assoc (v i) (v j) (eval v m)))))
        (compareIndex i j)) m

def mul (m n : Monomial) : Monomial :=
  Monomial.rec n (fun i _ r => insert i r) m

theorem eval_mul (v : Nat → Int) (m n : Monomial) :
    Eq (eval v (mul m n)) ((eval v m).mul (eval v n)) :=
  Monomial.rec (motive := fun m => Eq (eval v (mul m n)) ((eval v m).mul (eval v n)))
    (Int.one_mul (eval v n)).symm
    (fun i m ih => (eval_insert v i (mul m n)).trans
      ((congrArg (v i).mul ih).trans (Int.mul_assoc (v i) (eval v m) (eval v n)).symm)) m

def compare (a b : Monomial) : Ordering :=
  (Monomial.rec (motive := fun _ => Monomial → Ordering)
    (fun b => Monomial.rec .equal (fun _ _ _ => .less) b)
    (fun i _ cmp b => Monomial.rec .greater
      (fun j n _ => Ordering.rec .less (cmp n) .greater (compareIndex i j)) b) a) b

private theorem compare_factor_eq (i j : Nat) (tail : Ordering) :
    Eq (Ordering.rec (motive := fun _ => Ordering) .less tail .greater (compareIndex i j)) .equal →
      And (Eq i j) (Eq tail .equal) :=
  let law := fun (o : Ordering) => Eq (Ordering.rec (motive := fun _ => Ordering) .less tail .greater o) .equal →
    And (Eq o .equal) (Eq tail .equal)
  let h := Ordering.rec (motive := law)
    (fun h => False.elim (Eq.subst (Ordering.rec (motive := fun _ => Prop) True False True) h True.intro))
    (fun h => And.intro Eq.refl h)
    (fun h => False.elim (Eq.subst (Ordering.rec (motive := fun _ => Prop) True False True) h True.intro))
    (compareIndex i j)
  fun e => And.intro (compareIndex_eq i j (h e).left) (h e).right

theorem compare_eq (a b : Monomial) : Eq (compare a b) .equal → Eq a b :=
  (Monomial.rec (motive := fun a => ∀ b, Eq (compare a b) .equal → Eq a b)
    (fun b => Monomial.rec (motive := fun b => Eq (compare Monomial.one b) .equal → Eq Monomial.one b)
      (fun _ => Eq.refl)
      (fun _ _ _ h => False.elim (Eq.subst (Ordering.rec (motive := fun _ => Prop) True False True) h True.intro)) b)
    (fun i m ih b => Monomial.rec
      (motive := fun b => Eq (compare (Monomial.factor i m) b) .equal → Eq (Monomial.factor i m) b)
      (fun h => False.elim (Eq.subst (Ordering.rec (motive := fun _ => Prop) True False True) h True.intro))
      (fun j n _ e =>
        let h := compare_factor_eq i j (compare m n) e
        Eq.map₂ factor h.left (ih n h.right)) b) a) b

end Monomial
end Omega.Geometry.BargmannGram.Polynomial
