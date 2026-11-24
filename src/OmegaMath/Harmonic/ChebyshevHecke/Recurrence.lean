/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

Chebyshev recurrences over a commutative ring with a congruence.
- Chebyshev coordinates are powers of `x + s` for `s² = x² - 1`.
- The recurrence for even characters is expressed in the variable `κ = c²`.
-/

noncomputable section
@[expose] public section

namespace Omega.Chebyshev

variable {A : Type} {relation : A → A → Prop} (r : CommRingOps A relation)
variable (law : r.Laws)

def pair (a b : A) : Bool → A := fun flag => Bool.rec a b flag

def first (p : Bool → A) : A := p .false

def second (p : Bool → A) : A := p .true

/-- The sequence `a, b, t*b-a, …`. -/
def linear (t a b : A) (n : Nat) : A :=
  first (Nat.rec (pair a b) (fun _ p => pair (second p) (r.sub (r.mul t (second p)) (first p))) n)

theorem linear_zero (t a b : A) : Eq (linear r t a b .zero) a := Eq.refl

theorem linear_one (t a b : A) : Eq (linear r t a b (.succ .zero)) b := Eq.refl

theorem linear_step (t a b : A) (n : Nat) :
    Eq (linear r t a b n.succ.succ)
      (r.sub (r.mul t (linear r t a b n.succ)) (linear r t a b n)) := Eq.refl

include law in
/-- Uniqueness of a second-order recurrence, up to the ring congruence. -/
theorem linear_unique (t a b : A) (f : Nat → A)
    (h0 : r.eqv a (f .zero)) (h1 : r.eqv b (f (.succ .zero)))
    (step : ∀ n : Nat, r.eqv (r.sub (r.mul t (f n.succ)) (f n)) (f n.succ.succ))
    (n : Nat) : r.eqv (linear r t a b n) (f n) :=
  (Nat.rec (motive := fun n => And (r.eqv (linear r t a b n) (f n))
      (r.eqv (linear r t a b n.succ) (f n.succ)))
    (And.intro h0 h1)
    (fun k h => And.intro h.right
      (law.trans (law.sub_congr (law.mul_congr (law.refl t) h.right) h.left) (step k))) n).left

def step (x : A) (p : Bool → A) : Bool → A :=
  pair (r.add (r.mul x (first p)) (r.mul (r.sub (r.square x) r.one) (second p)))
    (r.add (first p) (r.mul x (second p)))

def state (x : A) (n : Nat) : Bool → A :=
  Nat.rec (pair r.one r.zero) (fun _ p => step r x p) n

/-- First-kind Chebyshev polynomial evaluated at `x`. -/
def T (x : A) (n : Nat) : A := first (state r x n)

/-- Second-kind coordinate with index shifted by one, with `V₀=0` and `Vₙ₊₁=Uₙ`. -/
def V (x : A) (n : Nat) : A := second (state r x n)

/-- Second-kind Chebyshev polynomial evaluated at `x`. -/
def U (x : A) (n : Nat) : A := V r x n.succ

/-- Coefficient of the two-step recurrence in the squared input. -/
def evenCoefficient (κ : A) : A :=
  r.sub (r.mul (r.square r.two) κ) r.two

/-- `Eₙ(κ)` is the polynomial giving the degree `2n` second-kind character. -/
def E (κ : A) (n : Nat) : A :=
  linear r (evenCoefficient r κ) r.one (r.sub (r.mul (r.square r.two) κ) r.one) n


open Polynomial

theorem T_zero (x : A) : Eq (T r x .zero) r.one := Eq.refl

theorem V_zero (x : A) : Eq (V r x .zero) r.zero := Eq.refl

theorem T_succ (x : A) (n : Nat) :
    Eq (T r x n.succ)
      (r.add (r.mul x (T r x n)) (r.mul (r.sub (r.square x) r.one) (V r x n))) := Eq.refl

theorem V_succ (x : A) (n : Nat) :
    Eq (V r x n.succ) (r.add (T r x n) (r.mul x (V r x n))) := Eq.refl

include law

theorem T_one (x : A) : r.eqv (T r x (.succ .zero)) x :=
  prove r law (.cons x (Variables.nil r)) ((e0.mul .one).add (((e0.square).sub .one).mul .zero)) e0 Eq.refl

theorem V_one (x : A) : r.eqv (V r x (.succ .zero)) r.one :=
  prove r law (.cons x (Variables.nil r)) (.add .one (e0.mul .zero)) .one Eq.refl

theorem T_step (x : A) (n : Nat) :
    r.eqv (T r x n.succ.succ) (r.sub (r.mul (r.mul r.two x) (T r x n.succ)) (T r x n)) :=
  let d := e0.square.sub .one
  let a := (e0.mul e1).add (d.mul e2)
  let b := e1.add (e0.mul e2)
  prove r law (.cons x (.cons (T r x n) (.cons (V r x n) (Variables.nil r))))
    ((e0.mul a).add (d.mul b)) (((Expr.two.mul e0).mul a).sub e1) Eq.refl

theorem V_step (x : A) (n : Nat) :
    r.eqv (V r x n.succ.succ) (r.sub (r.mul (r.mul r.two x) (V r x n.succ)) (V r x n)) :=
  let d := e0.square.sub .one
  let a := (e0.mul e1).add (d.mul e2)
  let b := e1.add (e0.mul e2)
  prove r law (.cons x (.cons (T r x n) (.cons (V r x n) (Variables.nil r))))
    (a.add (e0.mul b)) (((Expr.two.mul e0).mul b).sub e2) Eq.refl

theorem U_zero (x : A) : r.eqv (U r x .zero) r.one := V_one r law x

theorem U_one (x : A) : r.eqv (U r x (.succ .zero)) (r.mul r.two x) :=
  law.trans (V_step r law x .zero)
    (law.trans (law.sub_congr (law.mul_congr (law.refl (r.mul r.two x)) (V_one r law x)) (law.refl r.zero))
      (prove r law (.cons x (Variables.nil r)) (((Expr.two.mul e0).mul .one).sub .zero) (Expr.two.mul e0)
        Eq.refl))

theorem U_step (x : A) (n : Nat) :
    r.eqv (U r x n.succ.succ) (r.sub (r.mul (r.mul r.two x) (U r x n.succ)) (U r x n)) :=
  V_step r law x n.succ

private theorem norm_state (x : A) (n : Nat) :
    r.eqv (r.sub (r.square (T r x n)) (r.mul (r.sub (r.square x) r.one) (r.square (V r x n))))
      r.one :=
  Nat.rec (motive := fun n =>
    r.eqv (r.sub (r.square (T r x n)) (r.mul (r.sub (r.square x) r.one)
      (r.square (V r x n)))) r.one)
    (prove r law (.cons x (Variables.nil r)) (Expr.one.square.sub ((e0.square.sub .one).mul Expr.zero.square))
      .one Eq.refl)
    (fun k ih =>
      let d := e0.square.sub .one
      let a := (e0.mul e1).add (d.mul e2)
      let b := e1.add (e0.mul e2)
      law.trans (prove r law (.cons x (.cons (T r x k) (.cons (V r x k) (Variables.nil r))))
        (a.square.sub (d.mul b.square)) (e1.square.sub (d.mul e2.square)) Eq.refl) ih) n

theorem pell (x : A) (n : Nat) :
    r.eqv (r.sub (r.square (T r x n.succ)) (r.mul (r.sub (r.square x) r.one) (r.square (U r x n))))
      r.one := norm_state r law x n.succ

theorem add_indices (x : A) (m n : Nat) :
    And
      (r.eqv (T r x (m.add n))
        (r.add (r.mul (T r x m) (T r x n))
          (r.mul (r.sub (r.square x) r.one) (r.mul (V r x m) (V r x n)))))
      (r.eqv (V r x (m.add n))
        (r.add (r.mul (T r x m) (V r x n)) (r.mul (V r x m) (T r x n)))) :=
  let d := r.sub (r.square x) r.one
  let a := T r x m
  let b := V r x m
  let f := fun k => r.add (r.mul a (T r x k)) (r.mul d (r.mul b (V r x k)))
  let g := fun k => r.add (r.mul a (V r x k)) (r.mul b (T r x k))
  Nat.rec (motive := fun n => And (r.eqv (T r x (m.add n)) (f n))
      (r.eqv (V r x (m.add n)) (g n)))
    (And.intro
      (prove r law (.cons a (.cons b (.cons d (Variables.nil r)))) e0
        ((e0.mul .one).add (e2.mul (e1.mul .zero))) Eq.refl)
      (prove r law (.cons a (.cons b (Variables.nil r))) e1 ((e0.mul .zero).add (e1.mul .one)) Eq.refl))
    (fun k ih =>
      let c := T r x k
      let v := V r x k
      let vars := Variables.cons x (.cons d (.cons a (.cons b (.cons c (.cons v (Variables.nil r))))))
      let nextT := (e0.mul e4).add (e1.mul e5)
      let nextV := e4.add (e0.mul e5)
      let fk := (e2.mul e4).add (e1.mul (e3.mul e5))
      let gk := (e2.mul e5).add (e3.mul e4)
      And.intro
        (law.trans (law.add_congr (law.mul_congr (law.refl x) ih.left) (law.mul_congr (law.refl d) ih.right))
          (prove r law vars ((e0.mul fk).add (e1.mul gk))
            ((e2.mul nextT).add (e1.mul (e3.mul nextV))) Eq.refl))
        (law.trans (law.add_congr ih.left (law.mul_congr (law.refl x) ih.right))
          (prove r law vars (fk.add (e0.mul gk)) ((e2.mul nextV).add (e3.mul nextT)) Eq.refl))) n

theorem T_double (x : A) (n : Nat) :
    r.eqv (T r x (n.add n)) (r.sub (r.mul r.two (r.square (T r x n))) r.one) :=
  let a := T r x n
  let b := V r x n
  let d := r.sub (r.square x) r.one
  law.trans (add_indices r law x n n).left
    (law.trans (prove r law (.cons a (.cons b (.cons d (Variables.nil r))))
        (e0.square.add (e2.mul e1.square))
        ((Expr.two.mul e0.square).sub (e0.square.sub (e2.mul e1.square))) Eq.refl)
      (law.sub_congr (law.refl (r.mul r.two (r.square a))) (norm_state r law x n)))

theorem V_double (x : A) (n : Nat) :
    r.eqv (V r x (n.add n)) (r.mul r.two (r.mul (T r x n) (V r x n))) :=
  law.trans (add_indices r law x n n).right
    (prove r law (.cons (T r x n) (.cons (V r x n) (Variables.nil r)))
      ((e0.mul e1).add (e1.mul e0)) (Expr.two.mul (e0.mul e1)) Eq.refl)

theorem U_add (x : A) (m n : Nat) :
    r.eqv (U r x (m.add n).succ)
      (r.add (r.mul (T r x m.succ) (U r x n)) (r.mul (U r x m) (T r x n.succ))) :=
  Eq.subst (fun k => r.eqv (V r x k)
      (r.add (r.mul (T r x m.succ) (U r x n)) (r.mul (U r x m) (T r x n.succ))))
    (congrArg Nat.succ (Nat.succ_add m n)) (add_indices r law x m.succ n.succ).right

theorem U_double_odd (x : A) (n : Nat) :
    r.eqv (U r x (n.add n).succ) (r.mul r.two (r.mul (T r x n.succ) (U r x n))) :=
  Eq.subst (fun k => r.eqv (V r x k) (r.mul r.two (r.mul (T r x n.succ) (U r x n))))
    (congrArg Nat.succ (Nat.succ_add n n)) (V_double r law x n.succ)

theorem U_bridge (x : A) (n : Nat) :
    r.eqv (T r x n.succ) (r.sub (r.mul x (U r x n)) (V r x n)) :=
  let d := e0.square.sub .one
  prove r law (.cons x (.cons (T r x n) (.cons (V r x n) (Variables.nil r))))
    ((e0.mul e1).add (d.mul e2)) ((e0.mul (e1.add (e0.mul e2))).sub e2) Eq.refl

omit law in
theorem E_zero (κ : A) : Eq (E r κ .zero) r.one := Eq.refl

omit law in
theorem E_one (κ : A) :
    Eq (E r κ (.succ .zero)) (r.sub (r.mul (r.square r.two) κ) r.one) := Eq.refl

omit law in
theorem E_step (κ : A) (n : Nat) :
    Eq (E r κ n.succ.succ) (r.sub (r.mul (evenCoefficient r κ) (E r κ n.succ)) (E r κ n)) :=
  Eq.refl

/-- Four, eight and sixteen are obtained by repeated doubling. -/
theorem E_two (κ : A) :
    let four := r.square r.two
    let eight := r.mul r.two four
    r.eqv (E r κ (.succ (.succ .zero)))
      (r.add (r.sub (r.mul (r.square four) (r.square κ)) (r.mul (r.add eight four) κ)) r.one) :=
  let four := Expr.two.square
  let eight := Expr.two.mul four
  let q := four.mul e0
  prove r law (.cons κ (Variables.nil r)) (((q.sub Expr.two).mul (q.sub .one)).sub .one)
    (((four.square.mul e0.square).sub ((eight.add four).mul e0)).add .one) Eq.refl

omit law in
def double (n : Nat) : Nat := n.add n

omit law in
private theorem double_succ (n : Nat) : Eq (double n.succ) (double n).succ.succ :=
  congrArg Nat.succ (Nat.succ_add n n)

private theorem U_two_steps (x : A) (n : Nat) :
    r.eqv (r.sub (r.mul (evenCoefficient r (r.square x)) (U r x n.succ.succ)) (U r x n))
      (U r x n.succ.succ.succ.succ) :=
  let t := r.mul r.two x
  let a := U r x n
  let b := U r x n.succ
  let u₂ := r.sub (r.mul t b) a
  let u₃ := r.sub (r.mul t u₂) b
  have h₂ := U_step r law x n
  have h₃ : r.eqv (U r x n.succ.succ.succ) u₃ :=
    law.trans (U_step r law x n.succ) (law.sub_congr (law.mul_congr (law.refl t) h₂) (law.refl b))
  let tExpr := Expr.two.mul e0
  let qExpr := (Expr.two.square.mul e0.square).sub Expr.two
  let p₂ := (tExpr.mul e2).sub e1
  let p₃ := (tExpr.mul p₂).sub e2
  law.trans (law.sub_congr (law.mul_congr (law.refl (evenCoefficient r (r.square x))) h₂) (law.refl a))
    (law.trans (prove r law (.cons x (.cons a (.cons b (Variables.nil r))))
        ((qExpr.mul p₂).sub e1) ((tExpr.mul p₃).sub p₂) Eq.refl)
      (law.symm (law.trans (U_step r law x n.succ.succ) (law.sub_congr (law.mul_congr (law.refl t) h₃) h₂))))

theorem even_character (c : A) (n : Nat) :
    r.eqv (E r (r.square c) n) (U r c (n.add n)) :=
  let κ := r.square c
  let t := r.mul r.two c
  let q := evenCoefficient r κ
  have base : r.eqv (r.sub (r.mul (r.square r.two) κ) r.one) (U r c (.succ (.succ .zero))) :=
    law.symm (law.trans (U_step r law c .zero)
      (law.trans (law.sub_congr (law.mul_congr (law.refl t) (U_one r law c)) (U_zero r law c))
        (prove r law (.cons c (Variables.nil r)) (((Expr.two.mul e0).square).sub .one)
          ((Expr.two.square.mul e0.square).sub .one) Eq.refl)))
  linear_unique r law q r.one (r.sub (r.mul (r.square r.two) κ) r.one)
    (fun k => U r c (double k)) (law.symm (U_zero r law c)) base
    (fun k =>
      Eq.subst (fun j => r.eqv (r.sub (r.mul q (U r c (double k.succ))) (U r c (double k)))
        (U r c j)) (double_succ k.succ).symm
        (Eq.subst (fun j => r.eqv (r.sub (r.mul q (U r c j)) (U r c (double k)))
          (U r c j.succ.succ)) (double_succ k).symm (U_two_steps r law c (double k)))) n

omit law in
/-- The polynomial multiplying the signed input in the odd second-kind character. -/
def oddFactor (κ : A) (n : Nat) : A :=
  let q := evenCoefficient r κ
  linear r q r.two (r.mul r.two q) n

theorem odd_character (c : A) (n : Nat) :
    r.eqv (r.mul c (oddFactor r (r.square c) n)) (U r c (n.add n).succ) :=
  let κ := r.square c
  let q := evenCoefficient r κ
  let t := r.mul r.two c
  let f := fun k => r.mul c (oddFactor r κ k)
  let g := fun k => U r c (double k).succ
  have first : r.eqv (f .zero) (g .zero) := law.trans (law.mul_comm c r.two) (law.symm (U_one r law c))
  have second : r.eqv (f (.succ .zero)) (g (.succ .zero)) :=
    let tExpr := Expr.two.mul e0
    let qExpr := (Expr.two.square.mul e0.square).sub Expr.two
    have even := even_character r law c (.succ .zero)
    law.trans (prove r law (.cons c (Variables.nil r)) (e0.mul (Expr.two.mul qExpr))
        ((tExpr.mul (qExpr.add .one)).sub tExpr) Eq.refl)
      (law.symm (law.trans (U_step r law c (.succ .zero))
        (law.trans (law.sub_congr (law.mul_congr (law.refl t) (law.symm even)) (U_one r law c))
          (prove r law (.cons c (Variables.nil r))
            ((tExpr.mul ((Expr.two.square.mul e0.square).sub .one)).sub tExpr)
            ((tExpr.mul (qExpr.add .one)).sub tExpr) Eq.refl))))
  (Nat.rec (motive := fun k => And (r.eqv (f k) (g k)) (r.eqv (f k.succ) (g k.succ)))
    (And.intro first second)
    (fun k ih =>
      let s := oddFactor r κ k
      let v := oddFactor r κ k.succ
      have factor := prove r law (.cons c (.cons q (.cons s (.cons v (Variables.nil r)))))
        (e0.mul ((e1.mul e3).sub e2)) ((e1.mul (e0.mul e3)).sub (e0.mul e2)) Eq.refl
      have recurrence : r.eqv (r.sub (r.mul q (g k.succ)) (g k)) (g k.succ.succ) :=
        have firstIndex := congrArg Nat.succ (double_succ k)
        have secondIndex := (congrArg Nat.succ (double_succ k.succ)).trans
          (congrArg (fun j : Nat => j.succ.succ.succ) (double_succ k))
        Eq.subst (fun j : Nat => r.eqv (r.sub (r.mul q (g k.succ)) (g k)) (U r c j))
          secondIndex.symm
          (Eq.subst (fun j : Nat => r.eqv (r.sub (r.mul q (U r c j)) (g k))
            (U r c (double k).succ.succ.succ.succ.succ))
            firstIndex.symm (U_two_steps r law c (double k).succ))
      And.intro ih.right (law.trans factor
        (law.trans (law.sub_congr (law.mul_congr (law.refl q) ih.right) ih.left) recurrence))) n).left

end Omega.Chebyshev
