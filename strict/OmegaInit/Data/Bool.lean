/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Core

noncomputable section

@[expose] public section

namespace Omega.Bool

abbrev xor : Bool → Bool → Bool := fun a b => not (beq a b)

private theorem tabulate₂ {p : Bool → Bool → Prop}
    (ff : p false false) (ft : p false true) (tf : p true false) (tt : p true true) :
    ∀ x y, p x y :=
  Bool.rec (motive := fun x => ∀ y, p x y) (Bool.rec ff ft) (Bool.rec tf tt)

private theorem and_left_true (x y : Bool) : Eq (and x y) true → Eq x true :=
  tabulate₂ (p := fun x y => Eq (and x y) true → Eq x true)
    id id (fun _ => Omega.rfl) (fun _ => Omega.rfl) x y

private theorem and_right_true (x y : Bool) : Eq (and x y) true → Eq y true :=
  tabulate₂ (p := fun x y => Eq (and x y) true → Eq y true)
    id (fun _ => Omega.rfl) id (fun _ => Omega.rfl) x y

private def allBits (f : Bool → Bool) : Bool := and (f false) (f true)

private theorem atBit {f : Bool → Bool} (h : Eq (allBits f) true) (x : Bool) : Eq (f x) true :=
  Bool.rec (motive := fun x => Eq (f x) true)
    (and_left_true _ _ h) (and_right_true _ _ h) x

private theorem beq_sound (a b : Bool) : Eq (beq a b) true → Eq a b :=
  tabulate₂ (p := fun a b => Eq (beq a b) true → Eq a b)
    (fun _ => Omega.rfl) id (fun h => h.symm) (fun _ => Omega.rfl) a b

/-- Check equality of unary Boolean operations on both constructors. -/
private theorem unary {f g : Bool → Bool} (h : Eq (allBits (fun x => beq (f x) (g x))) true)
    (x : Bool) : Eq (f x) (g x) :=
  beq_sound _ _ (atBit h x)

/-- Check equality of binary Boolean operations on the four inputs. -/
private theorem binary {f g : Bool → Bool → Bool}
    (h : Eq (allBits (fun x => allBits (fun y => beq (f x y) (g x y)))) true)
    (x y : Bool) : Eq (f x y) (g x y) :=
  beq_sound _ _ (atBit (atBit h x) y)

/-- Check equality of ternary Boolean operations on the eight inputs. -/
private theorem ternary {f g : Bool → Bool → Bool → Bool}
    (h : Eq (allBits (fun x => allBits (fun y => allBits (fun z => beq (f x y z) (g x y z))))) true)
    (x y z : Bool) : Eq (f x y z) (g x y z) :=
  beq_sound _ _ (atBit (atBit (atBit h x) y) z)

theorem and_self_left : ∀ (a b : Bool), Eq (and a (and a b)) (and a b) :=
  binary Omega.rfl

theorem and_self_right : ∀ (a b : Bool), Eq (and (and a b) b) (and a b) :=
  binary Omega.rfl

theorem not_and_self : ∀ (x : Bool), Eq (and (not x) x) false :=
  unary Omega.rfl

theorem and_not_self : ∀ (x : Bool), Eq (and x (not x)) false :=
  unary Omega.rfl

theorem and_comm : ∀ (x y : Bool), Eq (and x y) (and y x) :=
  binary Omega.rfl

theorem and_left_comm : ∀ (x y z : Bool), Eq (and x (and y z)) (and y (and x z)) :=
  ternary Omega.rfl

theorem and_right_comm : ∀ (x y z : Bool), Eq (and (and x y) z) (and (and x z) y) :=
  ternary Omega.rfl

theorem or_self_left : ∀ (a b : Bool), Eq (or a (or a b)) (or a b) :=
  binary Omega.rfl

theorem or_self_right : ∀ (a b : Bool), Eq (or (or a b) b) (or a b) :=
  binary Omega.rfl

theorem not_or_self : ∀ (x : Bool), Eq (or (not x) x) true :=
  unary Omega.rfl

theorem or_not_self : ∀ (x : Bool), Eq (or x (not x)) true :=
  unary Omega.rfl

theorem or_comm : ∀ (x y : Bool), Eq (or x y) (or y x) :=
  binary Omega.rfl

theorem or_left_comm : ∀ (x y z : Bool), Eq (or x (or y z)) (or y (or x z)) :=
  ternary Omega.rfl

theorem or_right_comm : ∀ (x y z : Bool), Eq (or (or x y) z) (or (or x z) y) :=
  ternary Omega.rfl

theorem and_or_distrib_left : ∀ (x y z : Bool), Eq (and x (or y z)) (or (and x y) (and x z)) :=
  ternary Omega.rfl

theorem and_or_distrib_right : ∀ (x y z : Bool), Eq (and (or x y) z) (or (and x z) (and y z)) :=
  ternary Omega.rfl

theorem or_and_distrib_left : ∀ (x y z : Bool), Eq (or x (and y z)) (and (or x y) (or x z)) :=
  ternary Omega.rfl

theorem or_and_distrib_right : ∀ (x y z : Bool), Eq (or (and x y) z) (and (or x z) (or y z)) :=
  ternary Omega.rfl

theorem and_xor_distrib_left : ∀ (x y z : Bool), Eq (and x (xor y z)) (xor (and x y) (and x z)) :=
  ternary Omega.rfl

theorem and_xor_distrib_right : ∀ (x y z : Bool), Eq (and (xor x y) z) (xor (and x z) (and y z)) :=
  ternary Omega.rfl

theorem not_and : ∀ (x y : Bool), Eq (not (and x y)) (or (not x) (not y)) :=
  binary Omega.rfl

theorem not_or : ∀ (x y : Bool), Eq (not (or x y)) (and (not x) (not y)) :=
  binary Omega.rfl

theorem true_beq : ∀ (b : Bool), Eq (beq true b) b :=
  unary Omega.rfl

theorem false_beq : ∀ (b : Bool), Eq (beq false b) (not b) :=
  unary Omega.rfl

theorem true_bne : ∀ (b : Bool), Eq (xor true b) (not b) :=
  unary Omega.rfl

theorem false_bne : ∀ (b : Bool), Eq (xor false b) b :=
  unary Omega.rfl

theorem bne_true : ∀ (b : Bool), Eq (xor b true) (not b) :=
  unary Omega.rfl

theorem bne_false : ∀ (b : Bool), Eq (xor b false) b :=
  unary Omega.rfl

theorem not_beq_self : ∀ (x : Bool), Eq (beq (not x) x) false :=
  unary Omega.rfl

theorem beq_not_self : ∀ (x : Bool), Eq (beq x (not x)) false :=
  unary Omega.rfl

theorem not_bne : ∀ (a b : Bool), Eq (xor (not a) b) (not (xor a b)) :=
  binary Omega.rfl

theorem bne_not : ∀ (a b : Bool), Eq (xor a (not b)) (not (xor a b)) :=
  binary Omega.rfl

theorem not_bne_self : ∀ (x : Bool), Eq (xor (not x) x) true :=
  unary Omega.rfl

theorem bne_not_self : ∀ (x : Bool), Eq (xor x (not x)) true :=
  unary Omega.rfl

theorem beq_self_left : ∀ (a b : Bool), Eq (beq a (beq a b)) b :=
  binary Omega.rfl

theorem beq_self_right : ∀ (a b : Bool), Eq (beq (beq a b) b) a :=
  binary Omega.rfl

theorem bne_self_left : ∀ (a b : Bool), Eq (xor a (xor a b)) b :=
  binary Omega.rfl

theorem bne_self_right : ∀ (a b : Bool), Eq (xor (xor a b) b) a :=
  binary Omega.rfl

theorem not_bne_not : ∀ (x y : Bool), Eq (xor (not x) (not y)) (xor x y) :=
  binary Omega.rfl

theorem bne_assoc : ∀ (x y z : Bool), Eq (xor (xor x y) z) (xor x (xor y z)) :=
  ternary Omega.rfl

theorem false_xor : ∀ (x : Bool), Eq (xor false x) x :=
  unary Omega.rfl

theorem xor_false : ∀ (x : Bool), Eq (xor x false) x :=
  unary Omega.rfl

theorem true_xor : ∀ (x : Bool), Eq (xor true x) (not x) :=
  unary Omega.rfl

theorem xor_true : ∀ (x : Bool), Eq (xor x true) (not x) :=
  unary Omega.rfl

theorem not_xor_self : ∀ (x : Bool), Eq (xor (not x) x) true :=
  unary Omega.rfl

theorem xor_not_self : ∀ (x : Bool), Eq (xor x (not x)) true :=
  unary Omega.rfl

theorem not_xor : ∀ (x y : Bool), Eq (xor (not x) y) (not (xor x y)) :=
  binary Omega.rfl

theorem xor_not : ∀ (x y : Bool), Eq (xor x (not y)) (not (xor x y)) :=
  binary Omega.rfl

theorem not_xor_not : ∀ (x y : Bool), Eq (xor (not x) (not y)) (xor x y) :=
  binary Omega.rfl

theorem xor_self : ∀ (x : Bool), Eq (xor x x) false :=
  unary Omega.rfl

theorem xor_comm : ∀ (x y : Bool), Eq (xor x y) (xor y x) :=
  binary Omega.rfl

theorem xor_left_comm : ∀ (x y z : Bool), Eq (xor x (xor y z)) (xor y (xor x z)) :=
  ternary Omega.rfl

theorem xor_right_comm : ∀ (x y z : Bool), Eq (xor (xor x y) z) (xor (xor x z) y) :=
  ternary Omega.rfl

theorem xor_assoc : ∀ (x y z : Bool), Eq (xor (xor x y) z) (xor x (xor y z)) :=
  ternary Omega.rfl

theorem cond_true_left : ∀ (c f : Bool), Eq (cond c true f) (or c f) :=
  binary Omega.rfl

theorem cond_false_left : ∀ (c f : Bool), Eq (cond c false f) (and (not c) f) :=
  binary Omega.rfl

theorem cond_true_right : ∀ (c t : Bool), Eq (cond c t true) (or (not c) t) :=
  binary Omega.rfl

theorem cond_false_right : ∀ (c t : Bool), Eq (cond c t false) (and c t) :=
  binary Omega.rfl

theorem cond_not_self_left : ∀ (c b : Bool), Eq (cond c (not c) b) (and (not c) b) :=
  binary Omega.rfl

theorem cond_then_not_self : ∀ (c b : Bool), Eq (cond c (not c) b) (and (not c) b) :=
  binary Omega.rfl

theorem cond_not_self_right : ∀ (c b : Bool), Eq (cond c b (not c)) (or (not c) b) :=
  binary Omega.rfl

theorem cond_else_not_self : ∀ (c b : Bool), Eq (cond c b (not c)) (or (not c) b) :=
  binary Omega.rfl

theorem cond_self_left : ∀ (c b : Bool), Eq (cond c c b) (or c b) :=
  binary Omega.rfl

theorem cond_then_self : ∀ (c b : Bool), Eq (cond c c b) (or c b) :=
  binary Omega.rfl

theorem cond_self_right : ∀ (c b : Bool), Eq (cond c b c) (and c b) :=
  binary Omega.rfl

theorem cond_else_self : ∀ (c b : Bool), Eq (cond c b c) (and c b) :=
  binary Omega.rfl


/-! Evaluate propositional combinations of Boolean equalities by their two-valued truth tables. -/

private abbrev Represents (b : Bool) (p : Prop) := Iff (Eq b true) p

private theorem equals (x y : Bool) : Represents (beq x y) (Eq x y) :=
  Iff.intro (beq_sound x y) (fun h =>
    Eq.subst (motive := fun y => Eq (beq x y) true) h (Bool.rec Omega.rfl Omega.rfl x))

theorem false_ne_true : Ne false true := ne_true_of_eq_false Omega.rfl

private theorem conjunction {x y : Bool} {p q : Prop} (hp : Represents x p) (hq : Represents y q) :
    Represents (and x y) (And p q) :=
  Iff.intro (fun h => And.intro (hp.mp (and_left_true _ _ h)) (hq.mp (and_right_true _ _ h)))
    (fun h => (congrArg (fun x => and x y) (hp.mpr h.left)).trans (hq.mpr h.right))

private theorem disjunction {x y : Bool} {p q : Prop} (hp : Represents x p) (hq : Represents y q) :
    Represents (or x y) (Or p q) :=
  let liftOr : ∀ x y, Iff (Eq (or x y) true) (Or (Eq x true) (Eq y true)) :=
    tabulate₂
      (Iff.intro Or.inl (fun h => h.elim id id))
      (iff_of_true Omega.rfl (Or.inr Omega.rfl))
      (iff_of_true Omega.rfl (Or.inl Omega.rfl))
      (iff_of_true Omega.rfl (Or.inl Omega.rfl))
  Iff.trans (liftOr x y) (Iff.intro
    (fun h => h.elim (fun a => Or.inl (hp.mp a)) (fun b => Or.inr (hq.mp b)))
    (fun h => h.elim (fun a => Or.inl (hp.mpr a)) (fun b => Or.inr (hq.mpr b))))

private theorem negation {x : Bool} {p : Prop} (hp : Represents x p) : Represents (not x) (Not p) :=
  let flip : ∀ x, Iff (Eq (not x) true) (Not (Eq x true)) :=
    Bool.rec (motive := fun x => Iff (Eq (not x) true) (Not (Eq x true)))
      (iff_of_true Omega.rfl false_ne_true) (Iff.intro (fun h _ => false_ne_true h) (fun h => False.elim (h Omega.rfl)))
  Iff.intro (fun h p => ((flip x).mp h) (hp.mpr p))
    (fun h => (flip x).mpr (fun hx => h (hp.mp hx)))

private theorem implication {x y : Bool} {p q : Prop} (hp : Represents x p) (hq : Represents y q) :
    Represents (or (not x) y) (p → q) :=
  let cases := disjunction (negation hp) hq
  let split : Or (Eq x true) (Not (Eq x true)) :=
    Bool.rec (motive := fun x => Or (Eq x true) (Not (Eq x true)))
      (Or.inr false_ne_true) (Or.inl Omega.rfl) x
  Iff.intro (fun h a => (cases.mp h).elim (fun np => False.elim (np a)) id)
    (fun h => cases.mpr (split.elim (fun hx => Or.inr (h (hp.mp hx))) (fun hn => Or.inl (fun a => hn (hp.mpr a)))))

private theorem equivalence {x y : Bool} {p q : Prop} (hp : Represents x p) (hq : Represents y q) :
    Represents (and (or (not x) y) (or (not y) x)) (Iff p q) :=
  Iff.trans (conjunction (implication hp hq) (implication hq hp))
    (Iff.intro (fun h => Iff.intro h.left h.right) (fun h => And.intro h.mp h.mpr))

private theorem truth : Represents true True := iff_of_true Omega.rfl True.intro

private theorem falsity : Represents false False := Iff.intro false_ne_true False.elim

private theorem valid₁ {f : Bool → Bool} {p : Bool → Prop} (r : ∀ x, Represents (f x) (p x))
    (h : Eq (allBits f) true) (x : Bool) : p x := (r x).mp (atBit h x)

private theorem valid₂ {f : Bool → Bool → Bool} {p : Bool → Bool → Prop}
    (r : ∀ x y, Represents (f x y) (p x y)) (h : Eq (allBits (fun x => allBits (f x))) true)
    (x y : Bool) : p x y := (r x y).mp (atBit (atBit h x) y)

private theorem valid₃ {f : Bool → Bool → Bool → Bool} {p : Bool → Bool → Bool → Prop}
    (r : ∀ x y z, Represents (f x y z) (p x y z))
    (h : Eq (allBits (fun x => allBits (fun y => allBits (f x y)))) true)
    (x y z : Bool) : p x y z := (r x y z).mp (atBit (atBit (atBit h x) y) z)

theorem eq_false_or_eq_true (b : Bool) :
    Or (Eq b true) (Eq b false) :=
  valid₁ (fun b =>
    disjunction (equals b true) (equals b false)) Omega.rfl b

theorem eq_false_iff {b : Bool} :
    Iff (Eq b false) (Ne b true) :=
  valid₁ (fun b =>
    equivalence (equals b false) (negation (equals b true))) Omega.rfl b

theorem ne_false_iff {b : Bool} :
    Iff (Ne b false) (Eq b true) :=
  valid₁ (fun b =>
    equivalence (negation (equals b false)) (equals b true)) Omega.rfl b

theorem eq_iff_iff {a b : Bool} :
    Iff (Eq a b) (Iff (Eq a true) (Eq b true)) :=
  valid₂ (fun a b =>
    equivalence (equals a b) (equivalence (equals a true) (equals b true))) Omega.rfl a b

theorem eq_true_and_eq_false_self (b : Bool) :
    Iff (And (Eq b true) (Eq b false)) False :=
  valid₁ (fun b =>
    equivalence (conjunction (equals b true) (equals b false)) falsity) Omega.rfl b

theorem eq_false_and_eq_true_self (b : Bool) :
    Iff (And (Eq b false) (Eq b true)) False :=
  valid₁ (fun b =>
    equivalence (conjunction (equals b false) (equals b true)) falsity) Omega.rfl b

theorem and_eq_left_iff_imp {a b : Bool} :
    Iff (Eq (and a b) a) (Eq a true → Eq b true) :=
  valid₂ (fun a b =>
    equivalence (equals (and a b) a) (implication (equals a true) (equals b true))) Omega.rfl a b

theorem and_eq_right_iff_imp {a b : Bool} :
    Iff (Eq (and a b) b) (Eq b true → Eq a true) :=
  valid₂ (fun a b =>
    equivalence (equals (and a b) b) (implication (equals b true) (equals a true))) Omega.rfl a b

theorem eq_self_and {a b : Bool} :
    Iff (Eq a (and a b)) (Eq a true → Eq b true) :=
  valid₂ (fun a b =>
    equivalence (equals a (and a b)) (implication (equals a true) (equals b true))) Omega.rfl a b

theorem eq_and_self {a b : Bool} :
    Iff (Eq b (and a b)) (Eq b true → Eq a true) :=
  valid₂ (fun a b =>
    equivalence (equals b (and a b)) (implication (equals b true) (equals a true))) Omega.rfl a b

theorem not_and_eq_left_iff_and {a b : Bool} :
    Iff (Eq (and (not a) b) a) (And (Eq (not a) true) (Eq (not b) true)) :=
  valid₂ (fun a b =>
    equivalence (equals (and (not a) b) a) (conjunction (equals (not a) true) (equals (not b) true))) Omega.rfl a b

theorem and_not_eq_right_iff_and {a b : Bool} :
    Iff (Eq (and a (not b)) b) (And (Eq (not a) true) (Eq (not b) true)) :=
  valid₂ (fun a b =>
    equivalence (equals (and a (not b)) b) (conjunction (equals (not a) true) (equals (not b) true))) Omega.rfl a b

theorem eq_not_self_and {a b : Bool} :
    Iff (Eq a (and (not a) b)) (And (Eq (not a) true) (Eq (not b) true)) :=
  valid₂ (fun a b =>
    equivalence (equals a (and (not a) b)) (conjunction (equals (not a) true) (equals (not b) true))) Omega.rfl a b

theorem eq_and_not_self {a b : Bool} :
    Iff (Eq b (and a (not b))) (And (Eq (not a) true) (Eq (not b) true)) :=
  valid₂ (fun a b =>
    equivalence (equals b (and a (not b))) (conjunction (equals (not a) true) (equals (not b) true))) Omega.rfl a b

theorem eq_true_or_eq_false_self (b : Bool) :
    Iff (Or (Eq b true) (Eq b false)) True :=
  valid₁ (fun b =>
    equivalence (disjunction (equals b true) (equals b false)) truth) Omega.rfl b

theorem eq_false_or_eq_true_self (b : Bool) :
    Iff (Or (Eq b false) (Eq b true)) True :=
  valid₁ (fun b =>
    equivalence (disjunction (equals b false) (equals b true)) truth) Omega.rfl b

theorem or_eq_left_iff_imp {a b : Bool} :
    Iff (Eq (or a b) a) (Eq b true → Eq a true) :=
  valid₂ (fun a b =>
    equivalence (equals (or a b) a) (implication (equals b true) (equals a true))) Omega.rfl a b

theorem or_eq_right_iff_imp {a b : Bool} :
    Iff (Eq (or a b) b) (Eq a true → Eq b true) :=
  valid₂ (fun a b =>
    equivalence (equals (or a b) b) (implication (equals a true) (equals b true))) Omega.rfl a b

theorem eq_self_or {a b : Bool} :
    Iff (Eq a (or a b)) (Eq b true → Eq a true) :=
  valid₂ (fun a b =>
    equivalence (equals a (or a b)) (implication (equals b true) (equals a true))) Omega.rfl a b

theorem eq_or_self {a b : Bool} :
    Iff (Eq b (or a b)) (Eq a true → Eq b true) :=
  valid₂ (fun a b =>
    equivalence (equals b (or a b)) (implication (equals a true) (equals b true))) Omega.rfl a b

theorem not_or_eq_left_iff_and {a b : Bool} :
    Iff (Eq (or (not a) b) a) (And (Eq a true) (Eq b true)) :=
  valid₂ (fun a b =>
    equivalence (equals (or (not a) b) a) (conjunction (equals a true) (equals b true))) Omega.rfl a b

theorem or_not_eq_right_iff_and {a b : Bool} :
    Iff (Eq (or a (not b)) b) (And (Eq a true) (Eq b true)) :=
  valid₂ (fun a b =>
    equivalence (equals (or a (not b)) b) (conjunction (equals a true) (equals b true))) Omega.rfl a b

theorem eq_not_self_or {a b : Bool} :
    Iff (Eq a (or (not a) b)) (And (Eq a true) (Eq b true)) :=
  valid₂ (fun a b =>
    equivalence (equals a (or (not a) b)) (conjunction (equals a true) (equals b true))) Omega.rfl a b

theorem eq_or_not_self {a b : Bool} :
    Iff (Eq b (or a (not b))) (And (Eq a true) (Eq b true)) :=
  valid₂ (fun a b =>
    equivalence (equals b (or a (not b))) (conjunction (equals a true) (equals b true))) Omega.rfl a b

theorem and_eq_true_iff {x y : Bool} :
    Iff (Eq (and x y) true) (And (Eq x true) (Eq y true)) :=
  valid₂ (fun x y =>
    equivalence (equals (and x y) true) (conjunction (equals x true) (equals y true))) Omega.rfl x y

theorem and_eq_false_iff {x y : Bool} :
    Iff (Eq (and x y) false) (Or (Eq x false) (Eq y false)) :=
  valid₂ (fun x y =>
    equivalence (equals (and x y) false) (disjunction (equals x false) (equals y false))) Omega.rfl x y

theorem and_eq_false_imp {x y : Bool} :
    Iff (Eq (and x y) false) (Eq x true → Eq y false) :=
  valid₂ (fun x y =>
    equivalence (equals (and x y) false) (implication (equals x true) (equals y false))) Omega.rfl x y

theorem or_eq_true_iff {x y : Bool} :
    Iff (Eq (or x y) true) (Or (Eq x true) (Eq y true)) :=
  valid₂ (fun x y =>
    equivalence (equals (or x y) true) (disjunction (equals x true) (equals y true))) Omega.rfl x y

theorem or_eq_false_iff {x y : Bool} :
    Iff (Eq (or x y) false) (And (Eq x false) (Eq y false)) :=
  valid₂ (fun x y =>
    equivalence (equals (or x y) false) (conjunction (equals x false) (equals y false))) Omega.rfl x y

theorem not_eq_self (b : Bool) :
    Iff (Eq (not b) b) False :=
  valid₁ (fun b =>
    equivalence (equals (not b) b) falsity) Omega.rfl b

theorem eq_not_self (b : Bool) :
    Iff (Eq b (not b)) False :=
  valid₁ (fun b =>
    equivalence (equals b (not b)) falsity) Omega.rfl b

theorem bne_right_inj {x y z : Bool} :
    Iff (Eq (xor x y) (xor x z)) (Eq y z) :=
  valid₃ (fun x y z =>
    equivalence (equals (xor x y) (xor x z)) (equals y z)) Omega.rfl x y z

theorem bne_left_inj {x y z : Bool} :
    Iff (Eq (xor x z) (xor y z)) (Eq x y) :=
  valid₃ (fun x y z =>
    equivalence (equals (xor x z) (xor y z)) (equals x y)) Omega.rfl x y z

theorem eq_not_of_ne {x y : Bool} :
    Ne x y → Eq x (not y) :=
  valid₂ (fun x y =>
    implication (negation (equals x y)) (equals x (not y))) Omega.rfl x y

theorem eq_not {a b : Bool} :
    Iff (Eq a (not b)) (Ne a b) :=
  valid₂ (fun a b =>
    equivalence (equals a (not b)) (negation (equals a b))) Omega.rfl a b

theorem not_eq {a b : Bool} :
    Iff (Eq (not a) b) (Ne a b) :=
  valid₂ (fun a b =>
    equivalence (equals (not a) b) (negation (equals a b))) Omega.rfl a b

theorem coe_iff_coe {a b : Bool} :
    Iff (Iff (Eq a true) (Eq b true)) (Eq a b) :=
  valid₂ (fun a b =>
    equivalence (equivalence (equals a true) (equals b true)) (equals a b)) Omega.rfl a b

theorem coe_true_iff_false {a b : Bool} :
    Iff (Iff (Eq a true) (Eq b false)) (Eq a (not b)) :=
  valid₂ (fun a b =>
    equivalence (equivalence (equals a true) (equals b false)) (equals a (not b))) Omega.rfl a b

theorem coe_false_iff_true {a b : Bool} :
    Iff (Iff (Eq a false) (Eq b true)) (Eq (not a) b) :=
  valid₂ (fun a b =>
    equivalence (equivalence (equals a false) (equals b true)) (equals (not a) b)) Omega.rfl a b

theorem coe_false_iff_false {a b : Bool} :
    Iff (Iff (Eq a false) (Eq b false)) (Eq (not a) (not b)) :=
  valid₂ (fun a b =>
    equivalence (equivalence (equals a false) (equals b false)) (equals (not a) (not b))) Omega.rfl a b

theorem xor_right_inj {x y z : Bool} :
    Iff (Eq (xor x y) (xor x z)) (Eq y z) :=
  valid₃ (fun x y z =>
    equivalence (equals (xor x y) (xor x z)) (equals y z)) Omega.rfl x y z

theorem xor_left_inj {x y z : Bool} :
    Iff (Eq (xor x z) (xor y z)) (Eq x y) :=
  valid₃ (fun x y z =>
    equivalence (equals (xor x z) (xor y z)) (equals x y)) Omega.rfl x y z

theorem not_inj {x y : Bool} :
    Eq (not x) (not y) → Eq x y :=
  valid₂ (fun x y =>
    implication (equals (not x) (not y)) (equals x y)) Omega.rfl x y

theorem not_inj_iff {x y : Bool} :
    Iff (Eq (not x) (not y)) (Eq x y) :=
  valid₂ (fun x y =>
    equivalence (equals (not x) (not y)) (equals x y)) Omega.rfl x y

theorem and_or_inj_right {m x y : Bool} :
    Eq (and x m) (and y m) → Eq (or x m) (or y m) → Eq x y :=
  valid₃ (fun m x y =>
    implication (equals (and x m) (and y m)) (implication (equals (or x m) (or y m)) (equals x y))) Omega.rfl m x y

theorem and_or_inj_right_iff {m x y : Bool} :
    Iff (And (Eq (and x m) (and y m)) (Eq (or x m) (or y m))) (Eq x y) :=
  valid₃ (fun m x y =>
    equivalence (conjunction (equals (and x m) (and y m)) (equals (or x m) (or y m))) (equals x y)) Omega.rfl m x y

theorem and_or_inj_left {m x y : Bool} :
    Eq (and m x) (and m y) → Eq (or m x) (or m y) → Eq x y :=
  valid₃ (fun m x y =>
    implication (equals (and m x) (and m y)) (implication (equals (or m x) (or m y)) (equals x y))) Omega.rfl m x y

theorem and_or_inj_left_iff {m x y : Bool} :
    Iff (And (Eq (and m x) (and m y)) (Eq (or m x) (or m y))) (Eq x y) :=
  valid₃ (fun m x y =>
    equivalence (conjunction (equals (and m x) (and m y)) (equals (or m x) (or m y))) (equals x y)) Omega.rfl m x y

theorem eq_false_imp_eq_true {b : Bool} :
    Iff (Eq b false → Eq b true) (Eq b true) :=
  valid₁ (fun b =>
    equivalence (implication (equals b false) (equals b true)) (equals b true)) Omega.rfl b

theorem eq_true_imp_eq_false {b : Bool} :
    Iff (Eq b true → Eq b false) (Eq b false) :=
  valid₁ (fun b =>
    equivalence (implication (equals b true) (equals b false)) (equals b false)) Omega.rfl b

/-! Boolean order uses implication for ≤ and the conjunction of the negated lower
endpoint with the upper endpoint for <. -/

protected theorem eq_false_of_le_false {x : Bool} :
    ((Eq x true) → Eq false true) → Eq x false :=
  fun h => eq_false_of_ne_true (fun hx => false_ne_true (h hx))

protected theorem eq_true_of_true_le {x : Bool} :
    ((Eq true true) → Eq x true) → Eq x true :=
  fun h => h Omega.rfl

protected theorem false_le (x : Bool) :
    (Eq false true) → Eq x true :=
  fun h => False.elim (false_ne_true h)

protected theorem le_antisymm {x y : Bool} :
    ((Eq x true) → Eq y true) → ((Eq y true) → Eq x true) → Eq x y :=
  fun h₁ h₂ => coe_iff_coe.mp (Iff.intro h₁ h₂)

protected theorem le_of_eq {x y : Bool} :
    (Eq x y) → (Eq x true) → Eq y true :=
  fun h hx => h.symm.trans hx

protected theorem le_of_lt {x y : Bool} :
    (Eq (and (not x) y) true) → (Eq x true) → Eq y true :=
  valid₂ (fun x y =>
    implication (equals (and (not x) y) true) (implication (equals x true) (equals y true))) Omega.rfl x y

protected theorem le_of_lt_or_eq {x y : Bool} :
    (Or (Eq (and (not x) y) true) (Eq x y)) → (Eq x true) → Eq y true :=
  fun h => h.elim Bool.le_of_lt Bool.le_of_eq

protected theorem le_refl (x : Bool) :
    (Eq x true) → Eq x true :=
  id

protected theorem le_total (x y : Bool) :
    Or ((Eq x true) → Eq y true) ((Eq y true) → Eq x true) :=
  valid₂ (fun x y =>
    disjunction (implication (equals x true) (equals y true)) (implication (equals y true) (equals x true))) Omega.rfl x y

protected theorem le_trans {x y z : Bool} :
    ((Eq x true) → Eq y true) → ((Eq y true) → Eq z true) → (Eq x true) → Eq z true :=
  fun h₁ h₂ hx => h₂ (h₁ hx)

protected theorem le_true (x : Bool) :
    (Eq x true) → Eq true true :=
  fun _ => Omega.rfl

protected theorem lt_asymm {x y : Bool} :
    (Eq (and (not x) y) true) → Not (Eq (and (not y) x) true) :=
  valid₂ (fun x y =>
    implication (equals (and (not x) y) true) (negation (equals (and (not y) x) true))) Omega.rfl x y

protected theorem lt_iff_le_not_le {x y : Bool} :
    Iff (Eq (and (not x) y) true) (And ((Eq x true) → Eq y true) (Not ((Eq y true) → Eq x true))) :=
  valid₂ (fun x y =>
    equivalence (equals (and (not x) y) true)
      (conjunction (implication (equals x true) (equals y true))
        (negation (implication (equals y true) (equals x true))))) Omega.rfl x y

protected theorem lt_irrefl (x : Bool) :
    Not (Eq (and (not x) x) true) :=
  valid₁ (fun x =>
    negation (equals (and (not x) x) true)) Omega.rfl x

protected theorem lt_of_le_of_lt {x y z : Bool} :
    ((Eq x true) → Eq y true) → (Eq (and (not y) z) true) → Eq (and (not x) z) true :=
  valid₃ (fun x y z =>
    implication (implication (equals x true) (equals y true)) (implication (equals (and (not y) z) true) (equals (and (not x) z) true))) Omega.rfl x y z

protected theorem lt_of_le_of_ne {x y : Bool} :
    ((Eq x true) → Eq y true) → (Ne x y) → Eq (and (not x) y) true :=
  valid₂ (fun x y =>
    implication (implication (equals x true) (equals y true)) (implication (negation (equals x y)) (equals (and (not x) y) true))) Omega.rfl x y

protected theorem lt_of_lt_of_le {x y z : Bool} :
    (Eq (and (not x) y) true) → ((Eq y true) → Eq z true) → Eq (and (not x) z) true :=
  valid₃ (fun x y z =>
    implication (equals (and (not x) y) true) (implication (implication (equals y true) (equals z true)) (equals (and (not x) z) true))) Omega.rfl x y z

protected theorem lt_trans {x y z : Bool} :
    (Eq (and (not x) y) true) → (Eq (and (not y) z) true) → Eq (and (not x) z) true :=
  valid₃ (fun x y z =>
    implication (equals (and (not x) y) true) (implication (equals (and (not y) z) true) (equals (and (not x) z) true))) Omega.rfl x y z

protected theorem ne_of_lt {x y : Bool} :
    (Eq (and (not x) y) true) → Ne x y :=
  valid₂ (fun x y =>
    implication (equals (and (not x) y) true) (negation (equals x y))) Omega.rfl x y

theorem forall_bool {p : Bool → Prop} : Iff (∀ b, p b) (And (p false) (p true)) :=
  Iff.intro (fun h => And.intro (h false) (h true)) (fun h => Bool.rec h.left h.right)

theorem forall_bool' {p : Bool → Prop} (b : Bool) : Iff (∀ x, p x) (And (p b) (p (not b))) :=
  Bool.rec (motive := fun b => Iff (∀ x, p x) (And (p b) (p (not b))))
    forall_bool (Iff.trans forall_bool And.comm) b

theorem exists_bool {p : Bool → Prop} : Iff (Exists p) (Or (p false) (p true)) :=
  Iff.intro
    (fun h => h.elim (Bool.rec (motive := fun b => p b → Or (p false) (p true)) Or.inl Or.inr))
    (fun h => h.elim (Exists.intro false) (Exists.intro true))

theorem exists_bool' {p : Bool → Prop} (b : Bool) : Iff (Exists p) (Or (p b) (p (not b))) :=
  Bool.rec (motive := fun b => Iff (Exists p) (Or (p b) (p (not b))))
    exists_bool (Iff.trans exists_bool Or.comm) b

theorem cond_true {α : Sort u} {a b : α} : Eq (cond true a b) a := Omega.rfl

theorem cond_false {α : Sort u} {a b : α} : Eq (cond false a b) b := Omega.rfl

theorem cond_self (c : Bool) (t : α) : Eq (cond c t t) t :=
  Bool.rec (motive := fun c => Eq (cond c t t) t) Omega.rfl Omega.rfl c

theorem cond_not (b : Bool) (t e : α) : Eq (cond (not b) t e) (cond b e t) :=
  Bool.rec (motive := fun b => Eq (cond (not b) t e) (cond b e t)) Omega.rfl Omega.rfl b

theorem cond_pos {b : Bool} {a a' : α} (h : Eq b true) : Eq (cond b a a') a :=
  congrArg (fun b => cond b a a') h

theorem cond_neg {b : Bool} {a a' : α} (h : Eq b false) : Eq (cond b a a') a' :=
  congrArg (fun b => cond b a a') h

theorem apply_cond (f : α → β) {b : Bool} {a a' : α} :
    Eq (f (cond b a a')) (cond b (f a) (f a')) :=
  Bool.rec (motive := fun b => Eq (f (cond b a a')) (cond b (f a) (f a'))) Omega.rfl Omega.rfl b

end Omega.Bool

namespace Omega

theorem cond_true (a b : α) : Eq (cond Bool.true a b) a := Omega.rfl

theorem cond_false (a b : α) : Eq (cond Bool.false a b) b := Omega.rfl

theorem eq_false_of_ne_true {b : Bool} : Ne b Bool.true → Eq b Bool.false := Bool.eq_false_of_ne_true

theorem eq_true_of_ne_false {b : Bool} : Ne b Bool.false → Eq b Bool.true := Bool.eq_true_of_ne_false

theorem ne_false_of_eq_true {b : Bool} : Eq b Bool.true → Ne b Bool.false := Bool.ne_false_of_eq_true

theorem ne_true_of_eq_false {b : Bool} : Eq b Bool.false → Ne b Bool.true := Bool.ne_true_of_eq_false

end Omega

public section
namespace Bool
export _root_.Omega.Bool (and_comm and_eq_false_iff and_eq_false_imp and_eq_left_iff_imp and_eq_right_iff_imp and_eq_true_iff and_left_comm and_not_eq_right_iff_and and_not_self and_or_distrib_left and_or_distrib_right and_or_inj_left and_or_inj_left_iff and_or_inj_right and_or_inj_right_iff and_right_comm and_self_left and_self_right and_xor_distrib_left and_xor_distrib_right apply_cond beq_not_self beq_self_left beq_self_right bne_assoc bne_false bne_left_inj bne_not bne_not_self bne_right_inj bne_self_left bne_self_right bne_true coe_false_iff_false coe_false_iff_true coe_iff_coe coe_true_iff_false cond_else_not_self cond_else_self cond_false cond_false_left cond_false_right cond_neg cond_not cond_not_self_left cond_not_self_right cond_pos cond_self cond_self_left cond_self_right cond_then_not_self cond_then_self cond_true cond_true_left cond_true_right eq_and_not_self eq_and_self eq_false_and_eq_true_self eq_false_iff eq_false_imp_eq_true eq_false_of_le_false eq_false_or_eq_true eq_false_or_eq_true_self eq_iff_iff eq_not eq_not_of_ne eq_not_self eq_not_self_and eq_not_self_or eq_or_not_self eq_or_self eq_self_and eq_self_or eq_true_and_eq_false_self eq_true_imp_eq_false eq_true_of_true_le eq_true_or_eq_false_self exists_bool exists_bool' false_beq false_bne false_le false_ne_true false_xor forall_bool forall_bool' le_antisymm le_of_eq le_of_lt le_of_lt_or_eq le_refl le_total le_trans le_true lt_asymm lt_iff_le_not_le lt_irrefl lt_of_le_of_lt lt_of_le_of_ne lt_of_lt_of_le lt_trans ne_false_iff ne_of_lt not_and not_and_eq_left_iff_and not_and_self not_beq_self not_bne not_bne_not not_bne_self not_eq not_eq_self not_inj not_inj_iff not_or not_or_eq_left_iff_and not_or_self not_xor not_xor_not not_xor_self or_and_distrib_left or_and_distrib_right or_comm or_eq_false_iff or_eq_left_iff_imp or_eq_right_iff_imp or_eq_true_iff or_left_comm or_not_eq_right_iff_and or_not_self or_right_comm or_self_left or_self_right true_beq true_bne true_xor xor xor_assoc xor_comm xor_false xor_left_comm xor_left_inj xor_not xor_not_self xor_right_comm xor_right_inj xor_self xor_true)
end Bool
