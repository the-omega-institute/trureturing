module
prelude
public import OmegaMath.Algebra.QuadraticExt.Operations

/-!
Omega original.

The Fibonacci recurrence and the norm of powers of the golden generator.
-/

noncomputable section
@[expose] public section

namespace Omega.QuadPoly

variable {A : Type} {rel : A → A → Prop} (r : CommRingOps A rel)

def fibPair (n : Nat) : QuadPoly A r.one r.one :=
  Nat.rec (pair r.zero r.one) (fun _ prev =>
    pair prev.linear (r.add prev.scalar prev.linear)) n

def fibonacci (n : Nat) : A := (fibPair r n).scalar

theorem fib_zero : Eq (fibonacci r .zero) r.zero := Eq.refl
theorem fib_one : Eq (fibonacci r (.succ .zero)) r.one := Eq.refl
theorem fib_succ_succ (n : Nat) :
    Eq (fibonacci r n.succ.succ) (r.add (fibonacci r n) (fibonacci r n.succ)) := Eq.refl

def negOnePow (n : Nat) : A := Nat.rec r.one (fun _ prev => r.mul (r.neg r.one) prev) n

private theorem phi_times (law : r.Laws) (z : QuadPoly A r.one r.one) :
    Equivalent r (mul r (alpha r) z) (pair z.linear (r.add z.scalar z.linear)) :=
  let vars := Polynomial.Variables.cons z.scalar
    (Polynomial.Variables.cons z.linear (Polynomial.Variables.nil r))
  let a := Polynomial.e0
  let b := Polynomial.e1
  let o := Polynomial.Expr.one
  let z := Polynomial.Expr.zero
  And.intro
    (Polynomial.prove r law vars ((z.mul a).add (o.mul (o.mul b))) b Eq.refl)
    (Polynomial.prove r law vars (((z.mul b).add (o.mul a)).add (o.mul (o.mul b)))
      (a.add b) Eq.refl)

theorem phi_pow (law : r.Laws) (n : Nat) :
    Equivalent r (pow r (alpha (b := r.one) (c := r.one) r) n.succ)
      (pair (fibonacci r n) (fibonacci r n.succ)) :=
  let phi := alpha (b := r.one) (c := r.one) r
  Nat.rec (motive := fun n => Equivalent r (pow r phi n.succ) (fibPair r n))
    (mul_one law phi)
    (fun n ih => trans law (mul_congr law (refl law phi) ih) (phi_times r law (fibPair r n))) n

theorem norm_phi_pow (law : r.Laws) (n : Nat) :
    r.eqv (norm r (pow r (alpha (b := r.one) (c := r.one) r) n)) (negOnePow r n) :=
  let phi := alpha (b := r.one) (c := r.one) r
  Nat.rec (motive := fun n => r.eqv (norm r (pow r phi n)) (negOnePow r n))
    (norm_one (b := r.one) (c := r.one) law)
    (fun n ih => law.trans (norm_mul law phi (pow r phi n))
      (law.mul_congr (norm_alpha (b := r.one) (c := r.one) law) ih)) n

end Omega.QuadPoly
