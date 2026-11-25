module
prelude
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Commutative ring operations with a congruence, interpreted by integer equality
or by cross multiplication of finite signed fractions.
-/

noncomputable section
@[expose] public section

namespace Omega

structure CommRingOps (A : Type) (relation : A → A → Prop) where
  constant : Bool → A
  add : A → A → A
  mul : A → A → A
  neg : A → A
namespace CommRingOps

variable {A : Type} {relation : A → A → Prop} (r : CommRingOps A relation)

def eqv (_ : CommRingOps A relation) := relation

def zero : A := r.constant .false
def one : A := r.constant .true

def sub (a b : A) : A := r.add a (r.neg b)
def square (a : A) : A := r.mul a a
def two : A := r.add r.one r.one

def Laws : Prop :=
  ∀ result : Prop,
    ((∀ a, r.eqv a a) →
     (∀ {a b}, r.eqv a b → r.eqv b a) →
     (∀ {a b c}, r.eqv a b → r.eqv b c → r.eqv a c) →
     (∀ {a b c d}, r.eqv a b → r.eqv c d → r.eqv (r.add a c) (r.add b d)) →
     (∀ {a b c d}, r.eqv a b → r.eqv c d → r.eqv (r.mul a c) (r.mul b d)) →
     (∀ {a b}, r.eqv a b → r.eqv (r.neg a) (r.neg b)) →
     (∀ a b, r.eqv (r.add a b) (r.add b a)) →
     (∀ a b c, r.eqv (r.add (r.add a b) c) (r.add a (r.add b c))) →
     (∀ a, r.eqv (r.add a (r.constant .false)) a) →
     (∀ a, r.eqv (r.add a (r.neg a)) (r.constant .false)) →
     (∀ a b, r.eqv (r.mul a b) (r.mul b a)) →
     (∀ a b c, r.eqv (r.mul (r.mul a b) c) (r.mul a (r.mul b c))) →
     (∀ a, r.eqv (r.mul a (r.constant .true)) a) →
     (∀ a, r.eqv (r.mul a (r.constant .false)) (r.constant .false)) →
     (∀ a b c, r.eqv (r.mul a (r.add b c)) (r.add (r.mul a b) (r.mul a c))) → result) → result

namespace Laws

variable {r}

theorem intro
    (h_refl : ∀ a, r.eqv a a)
    (h_symm : ∀ {a b}, r.eqv a b → r.eqv b a)
    (h_trans : ∀ {a b c}, r.eqv a b → r.eqv b c → r.eqv a c)
    (h_add_congr : ∀ {a b c d}, r.eqv a b → r.eqv c d → r.eqv (r.add a c) (r.add b d))
    (h_mul_congr : ∀ {a b c d}, r.eqv a b → r.eqv c d → r.eqv (r.mul a c) (r.mul b d))
    (h_neg_congr : ∀ {a b}, r.eqv a b → r.eqv (r.neg a) (r.neg b))
    (h_add_comm : ∀ a b, r.eqv (r.add a b) (r.add b a))
    (h_add_assoc : ∀ a b c, r.eqv (r.add (r.add a b) c) (r.add a (r.add b c)))
    (h_add_zero : ∀ a, r.eqv (r.add a (r.constant .false)) a)
    (h_add_neg : ∀ a, r.eqv (r.add a (r.neg a)) (r.constant .false))
    (h_mul_comm : ∀ a b, r.eqv (r.mul a b) (r.mul b a))
    (h_mul_assoc : ∀ a b c, r.eqv (r.mul (r.mul a b) c) (r.mul a (r.mul b c)))
    (h_mul_one : ∀ a, r.eqv (r.mul a (r.constant .true)) a)
    (h_mul_zero : ∀ a, r.eqv (r.mul a (r.constant .false)) (r.constant .false))
    (h_mul_add : ∀ a b c, r.eqv (r.mul a (r.add b c)) (r.add (r.mul a b) (r.mul a c)))
    : r.Laws :=
  fun _ use => use h_refl h_symm h_trans h_add_congr h_mul_congr h_neg_congr h_add_comm h_add_assoc h_add_zero h_add_neg h_mul_comm h_mul_assoc h_mul_one h_mul_zero h_mul_add

theorem refl (law : r.Laws) : ∀ a, r.eqv a a :=
  law _ (fun h _ _ _ _ _ _ _ _ _ _ _ _ _ _ => h)

theorem symm (law : r.Laws) : ∀ {a b}, r.eqv a b → r.eqv b a :=
  law _ (fun _ h _ _ _ _ _ _ _ _ _ _ _ _ _ => h)

theorem trans (law : r.Laws) : ∀ {a b c}, r.eqv a b → r.eqv b c → r.eqv a c :=
  law _ (fun _ _ h _ _ _ _ _ _ _ _ _ _ _ _ => h)

theorem add_congr (law : r.Laws) : ∀ {a b c d}, r.eqv a b → r.eqv c d → r.eqv (r.add a c) (r.add b d) :=
  law _ (fun _ _ _ h _ _ _ _ _ _ _ _ _ _ _ => h)

theorem mul_congr (law : r.Laws) : ∀ {a b c d}, r.eqv a b → r.eqv c d → r.eqv (r.mul a c) (r.mul b d) :=
  law _ (fun _ _ _ _ h _ _ _ _ _ _ _ _ _ _ => h)

theorem neg_congr (law : r.Laws) : ∀ {a b}, r.eqv a b → r.eqv (r.neg a) (r.neg b) :=
  law _ (fun _ _ _ _ _ h _ _ _ _ _ _ _ _ _ => h)

theorem add_comm (law : r.Laws) : ∀ a b, r.eqv (r.add a b) (r.add b a) :=
  law _ (fun _ _ _ _ _ _ h _ _ _ _ _ _ _ _ => h)

theorem add_assoc (law : r.Laws) : ∀ a b c, r.eqv (r.add (r.add a b) c) (r.add a (r.add b c)) :=
  law _ (fun _ _ _ _ _ _ _ h _ _ _ _ _ _ _ => h)

theorem add_zero (law : r.Laws) : ∀ a, r.eqv (r.add a (r.constant .false)) a :=
  law _ (fun _ _ _ _ _ _ _ _ h _ _ _ _ _ _ => h)

theorem add_neg (law : r.Laws) : ∀ a, r.eqv (r.add a (r.neg a)) (r.constant .false) :=
  law _ (fun _ _ _ _ _ _ _ _ _ h _ _ _ _ _ => h)

theorem mul_comm (law : r.Laws) : ∀ a b, r.eqv (r.mul a b) (r.mul b a) :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ h _ _ _ _ => h)

theorem mul_assoc (law : r.Laws) : ∀ a b c, r.eqv (r.mul (r.mul a b) c) (r.mul a (r.mul b c)) :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ h _ _ _ => h)

theorem mul_one (law : r.Laws) : ∀ a, r.eqv (r.mul a (r.constant .true)) a :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => h)

theorem mul_zero (law : r.Laws) : ∀ a, r.eqv (r.mul a (r.constant .false)) (r.constant .false) :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => h)

theorem mul_add (law : r.Laws) : ∀ a b c, r.eqv (r.mul a (r.add b c)) (r.add (r.mul a b) (r.mul a c)) :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h)

end Laws

namespace Laws

variable {r} (law : r.Laws)
include law

theorem zero_add (a : A) : r.eqv (r.add r.zero a) a :=
  law.trans (law.add_comm r.zero a) (law.add_zero a)

theorem one_mul (a : A) : r.eqv (r.mul r.one a) a :=
  law.trans (law.mul_comm r.one a) (law.mul_one a)

theorem zero_mul (a : A) : r.eqv (r.mul r.zero a) r.zero :=
  law.trans (law.mul_comm r.zero a) (law.mul_zero a)

theorem add_mul (a b c : A) : r.eqv (r.mul (r.add a b) c) (r.add (r.mul a c) (r.mul b c)) :=
  law.trans (law.mul_comm (r.add a b) c) (law.trans (law.mul_add c a b)
    (law.add_congr (law.mul_comm c a) (law.mul_comm c b)))

theorem add_add_add_comm (a b c d : A) :
    r.eqv (r.add (r.add a b) (r.add c d)) (r.add (r.add a c) (r.add b d)) :=
  law.trans (law.add_assoc a b (r.add c d))
    (law.trans (law.add_congr (law.refl a) (law.trans (law.symm (law.add_assoc b c d))
      (law.trans (law.add_congr (law.add_comm b c) (law.refl d)) (law.add_assoc c b d))))
      (law.symm (law.add_assoc a c (r.add b d))))

theorem add_left_cancel {a b c : A} (h : r.eqv (r.add a b) (r.add a c)) : r.eqv b c :=
  have cancel (x : A) : r.eqv (r.add (r.neg a) (r.add a x)) x :=
    law.trans (law.symm (law.add_assoc (r.neg a) a x))
      (law.trans (law.add_congr (law.trans (law.add_comm (r.neg a) a) (law.add_neg a)) (law.refl x))
        (law.zero_add x))
  law.trans (law.symm (cancel b)) (law.trans (law.add_congr (law.refl (r.neg a)) h) (cancel c))

theorem eq_neg_of_add_eq_zero {a b : A} (h : r.eqv (r.add a b) r.zero) : r.eqv b (r.neg a) :=
  law.add_left_cancel (law.trans h (law.symm (law.add_neg a)))

theorem neg_zero : r.eqv (r.neg r.zero) r.zero :=
  law.symm (law.eq_neg_of_add_eq_zero (law.add_zero r.zero))

theorem neg_neg (a : A) : r.eqv (r.neg (r.neg a)) a :=
  law.symm (law.eq_neg_of_add_eq_zero (law.trans (law.add_comm (r.neg a) a) (law.add_neg a)))

theorem neg_add (a b : A) : r.eqv (r.neg (r.add a b)) (r.add (r.neg a) (r.neg b)) :=
  law.symm (law.eq_neg_of_add_eq_zero (law.trans (law.add_add_add_comm a b (r.neg a) (r.neg b))
    (law.trans (law.add_congr (law.add_neg a) (law.add_neg b)) (law.add_zero r.zero))))

theorem mul_neg (a b : A) : r.eqv (r.mul a (r.neg b)) (r.neg (r.mul a b)) :=
  law.eq_neg_of_add_eq_zero (law.trans (law.symm (law.mul_add a b (r.neg b)))
    (law.trans (law.mul_congr (law.refl a) (law.add_neg b)) (law.mul_zero a)))

theorem neg_mul (a b : A) : r.eqv (r.mul (r.neg a) b) (r.neg (r.mul a b)) :=
  law.trans (law.mul_comm (r.neg a) b) (law.trans (law.mul_neg b a) (law.neg_congr (law.mul_comm b a)))

theorem sub_congr {a b c d : A} (h : r.eqv a b) (k : r.eqv c d) :
    r.eqv (r.sub a c) (r.sub b d) :=
  law.add_congr h (law.neg_congr k)

end Laws

end CommRingOps

def intRing : CommRingOps Int Eq where
  constant := fun k => Bool.rec Int.zero Int.one k
  add := Int.add
  mul := Int.mul
  neg := Int.neg

theorem intRingLaws : intRing.Laws :=
  CommRingOps.Laws.intro
    (fun _ => Eq.refl)
    (Eq.symm)
    (Eq.trans)
    (Eq.map₂ Int.add)
    (Eq.map₂ Int.mul)
    (congrArg Int.neg)
    (Int.add_comm)
    (Int.add_assoc)
    (Int.add_zero)
    (Int.add_right_neg)
    (Int.mul_comm)
    (Int.mul_assoc)
    (Int.mul_one)
    (Int.mul_zero)
    (Int.mul_add)

/-- The finite part of IntRatio with its original numerator and positive denominator. -/
structure FiniteRatio where
  num : Int
  denPred : Nat

namespace FiniteRatio

def toRatio (x : FiniteRatio) : IntRatio := .fraction x.num x.denPred
def ofInt (n : Int) : FiniteRatio := ⟨n, .zero⟩
def zero : FiniteRatio := ofInt Int.zero
def one : FiniteRatio := ofInt Int.one
def add (x y : FiniteRatio) : FiniteRatio :=
  ⟨(x.num.mul (IntRatio.denominator y.denPred)).add
    (y.num.mul (IntRatio.denominator x.denPred)), IntRatio.mulDenPred x.denPred y.denPred⟩
def mul (x y : FiniteRatio) : FiniteRatio :=
  ⟨x.num.mul y.num, IntRatio.mulDenPred x.denPred y.denPred⟩
def neg (x : FiniteRatio) : FiniteRatio := ⟨x.num.neg, x.denPred⟩
def sub (x y : FiniteRatio) : FiniteRatio := x.add y.neg
def square (x : FiniteRatio) : FiniteRatio := x.mul x
def Equivalent (x y : FiniteRatio) : Prop := IntRatio.Equivalent x.toRatio y.toRatio
def Le (x y : FiniteRatio) : Prop := IntRatio.Le x.toRatio y.toRatio
def Lt (x y : FiniteRatio) : Prop := IntRatio.Lt x.toRatio y.toRatio

/-- A finite representative of the reciprocal, equal to zero at zero. -/
def inv (x : FiniteRatio) : FiniteRatio :=
  let d := IntRatio.denominator x.denPred
  Int.rec (motive := fun _ => FiniteRatio)
    (fun n => Nat.rec zero (fun k _ => ⟨d, k⟩) n)
    (fun k => ⟨d.neg, k⟩) x.num

theorem inv_toRatio (x : FiniteRatio) (h : Not (Eq x.num Int.zero)) :
    Eq x.inv.toRatio x.toRatio.inv :=
  let P := fun (a : Int) => ∀ d, Not (Eq a Int.zero) →
    Eq (inv ⟨a, d⟩).toRatio (toRatio ⟨a, d⟩).inv
  (Int.rec (motive := P)
    (fun n => Nat.rec (motive := fun n => P (Int.ofNat n))
      (fun _ h => False.elim (h Eq.refl)) (fun _ _ _ _ => Eq.refl) n)
    (fun _ _ _ => Eq.refl) x.num) x.denPred h

theorem mul_inv_cancel (x : FiniteRatio) (h : Not (Eq x.num Int.zero)) :
    Equivalent (x.mul x.inv) one :=
  Eq.subst (fun y => IntRatio.Equivalent (x.toRatio.mul y) one.toRatio)
    (x.inv_toRatio h).symm (IntRatio.mul_inv_cancel x.num x.denPred h)

theorem mul_zero (x : FiniteRatio) : Equivalent (x.mul zero) zero :=
  ((Int.mul_one (x.num.mul Int.zero)).trans (Int.mul_zero x.num)).trans (Int.zero_mul (IntRatio.denominator (x.mul zero).denPred)).symm

end FiniteRatio

def rationalRing : CommRingOps FiniteRatio FiniteRatio.Equivalent where
  constant := fun k => Bool.rec FiniteRatio.zero FiniteRatio.one k
  add := FiniteRatio.add
  mul := FiniteRatio.mul
  neg := FiniteRatio.neg

theorem rationalRingLaws : rationalRing.Laws :=
  CommRingOps.Laws.intro (r := rationalRing)
    (fun x => IntRatio.equivalent_refl x.toRatio)
    (fun {x y} => IntRatio.Equivalent.symm (x := x.toRatio) (y := y.toRatio))
    (fun {x y z} => IntRatio.Equivalent.trans (x := x.toRatio) (y := y.toRatio) (z := z.toRatio))
    (fun {a b c d} => IntRatio.add_congr
    (x := a.toRatio) (y := b.toRatio) (z := c.toRatio) (w := d.toRatio))
    (fun {a b c d} => IntRatio.mul_congr
    (x := a.toRatio) (y := b.toRatio) (z := c.toRatio) (w := d.toRatio))
    (fun {a b} => IntRatio.neg_congr (x := a.toRatio) (y := b.toRatio))
    (fun x y => IntRatio.add_comm x.toRatio y.toRatio)
    (fun x y z => IntRatio.add_assoc x.toRatio y.toRatio z.toRatio)
    (fun x => IntRatio.add_zero x.toRatio)
    (fun x => IntRatio.add_neg x.num x.denPred)
    (fun x y => IntRatio.mul_comm x.toRatio y.toRatio)
    (fun x y z => IntRatio.mul_assoc x.toRatio y.toRatio z.toRatio)
    (fun x => IntRatio.mul_one x.toRatio)
    (FiniteRatio.mul_zero)
    (fun x y z => IntRatio.mul_add x.toRatio y.toRatio z.toRatio)

end Omega
