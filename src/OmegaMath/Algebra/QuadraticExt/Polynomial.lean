module
prelude
public import OmegaMath.Algebra.QuadraticExt.Polynomial.Monomials

/-!
Omega original.

A kernel-checked commutative polynomial certificate. Expanding both sides
and moving the negative monomials across the equality reduces the check
to equality of ordered lists of positive monomials.
-/

noncomputable section
@[expose] public section

namespace Omega.Polynomial

inductive Expr where
  | zero
  | one
  | var (i : Nat)
  | add (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)

def Expr.sub (a b : Expr) : Expr := a.add b.neg
def Expr.square (a : Expr) : Expr := a.mul a
def Expr.two : Expr := .add .one .one

def e0 : Expr := .var .zero
def e1 : Expr := .var (.succ .zero)
def e2 : Expr := .var (.succ (.succ .zero))
def e3 : Expr := .var (.succ (.succ (.succ .zero)))
def e4 : Expr := .var (.succ (.succ (.succ (.succ .zero))))
def e5 : Expr := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
def e6 : Expr := .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
def e7 : Expr := .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))

inductive Terms where
  | nil
  | cons (negative : Bool) (monomial : Word) (rest : Terms)

namespace Terms

def append (a b : Terms) : Terms :=
  Terms.rec b (fun sign word _ rest => .cons sign word rest) a

def flip (sign : Bool) : Bool := Bool.rec .true .false sign

def neg (a : Terms) : Terms :=
  Terms.rec .nil (fun sign word _ rest => .cons (flip sign) word rest) a

def product (sign : Bool) (word : Word) (b : Terms) : Terms :=
  Terms.rec .nil (fun s w _ rest =>
    .cons (Bool.rec (motive := fun _ => Bool) s (flip s) sign) (word.mul w) rest) b

def mul (a b : Terms) : Terms :=
  Terms.rec .nil (fun sign word _ rest => (product sign word b).append rest) a

def positives (a : Terms) : Words :=
  Terms.rec .nil (fun sign word _ rest => Bool.rec (Words.cons word rest) rest sign) a

def negatives (a : Terms) : Words :=
  Terms.rec .nil (fun sign word _ rest => Bool.rec rest (Words.cons word rest) sign) a

variable {A : Type} {rel : A → A → Prop} (r : CommRingOps A rel) (vars : Variables A)

def signed (sign : Bool) (a : A) : A := Bool.rec a (r.neg a) sign

def eval (a : Terms) : A :=
  Terms.rec r.zero (fun sign word _ rest => r.add (signed r sign (word.eval r vars)) rest) a

variable {r vars} (law : r.Laws)
include law

private theorem signed_congr (sign : Bool) {a b : A} (h : r.eqv a b) :
    r.eqv (signed r sign a) (signed r sign b) :=
  Bool.rec (motive := fun s => r.eqv (signed r s a) (signed r s b))
    h (law.neg_congr h) sign

private theorem signed_flip (sign : Bool) (a : A) :
    r.eqv (signed r (flip sign) a) (r.neg (signed r sign a)) :=
  Bool.rec (motive := fun s => r.eqv (signed r (flip s) a) (r.neg (signed r s a)))
    (law.refl (r.neg a)) (law.symm (law.neg_neg a)) sign

private theorem signed_product (s t : Bool) (a b : A) :
    r.eqv (signed r (Bool.rec (motive := fun _ => Bool) t (flip t) s) (r.mul a b))
      (r.mul (signed r s a) (signed r t b)) :=
  Bool.rec (motive := fun s => r.eqv (signed r (Bool.rec (motive := fun _ => Bool) t (flip t) s) (r.mul a b))
    (r.mul (signed r s a) (signed r t b)))
    (Bool.rec (motive := fun t => r.eqv (signed r t (r.mul a b)) (r.mul a (signed r t b)))
      (law.refl (r.mul a b)) (law.symm (law.mul_neg a b)) t)
    (law.trans (signed_flip law t (r.mul a b))
      (law.trans (law.neg_congr
        (Bool.rec (motive := fun t => r.eqv (signed r t (r.mul a b)) (r.mul a (signed r t b)))
          (law.refl (r.mul a b)) (law.symm (law.mul_neg a b)) t))
        (law.symm (law.neg_mul a (signed r t b))))) s

theorem eval_append (a b : Terms) :
    r.eqv (eval r vars (a.append b)) (r.add (eval r vars a) (eval r vars b)) :=
  Terms.rec (motive := fun a =>
    r.eqv (eval r vars (a.append b)) (r.add (eval r vars a) (eval r vars b)))
    (law.symm (law.zero_add _)) (fun s w tail ih =>
      let x := signed r s (w.eval r vars)
      law.trans (law.add_congr (law.refl x) ih)
        (law.symm (law.add_assoc x (eval r vars tail) (eval r vars b)))) a

theorem eval_neg (a : Terms) :
    r.eqv (eval r vars a.neg) (r.neg (eval r vars a)) :=
  Terms.rec (motive := fun a => r.eqv (eval r vars a.neg) (r.neg (eval r vars a)))
    (law.symm law.neg_zero) (fun s w tail ih =>
      law.trans (law.add_congr (signed_flip law s (w.eval r vars)) ih)
        (law.symm (law.neg_add (signed r s (w.eval r vars)) (eval r vars tail)))) a

private theorem eval_product (s : Bool) (w : Word) (b : Terms) :
    r.eqv (eval r vars (product s w b)) (r.mul (signed r s (w.eval r vars)) (eval r vars b)) :=
  let x := signed r s (w.eval r vars)
  Terms.rec (motive := fun b => r.eqv (eval r vars (product s w b)) (r.mul x (eval r vars b)))
    (law.symm (law.mul_zero x)) (fun t k tail ih =>
      have factor := signed_congr law (Bool.rec (motive := fun _ => Bool) t (flip t) s) (Word.eval_mul (vars := vars) law w k)
      have sign := signed_product law s t (w.eval r vars) (k.eval r vars)
      law.trans (law.add_congr (law.trans factor sign) ih)
        (law.symm (law.mul_add x (signed r t (k.eval r vars)) (eval r vars tail)))) b

theorem eval_mul (a b : Terms) :
    r.eqv (eval r vars (a.mul b)) (r.mul (eval r vars a) (eval r vars b)) :=
  Terms.rec (motive := fun a =>
    r.eqv (eval r vars (a.mul b)) (r.mul (eval r vars a) (eval r vars b)))
    (law.symm (law.zero_mul _)) (fun s w tail ih =>
      law.trans (eval_append (vars := vars) law (product s w b) (tail.mul b))
        (law.trans (law.add_congr (eval_product (vars := vars) law s w b) ih)
          (law.symm (law.add_mul (signed r s (w.eval r vars)) (eval r vars tail) (eval r vars b))))) a

/-- Adding the negative monomials back recovers the positive monomials. -/
theorem eval_split (a : Terms) :
    r.eqv (r.add (eval r vars a) (a.negatives.eval r vars)) (a.positives.eval r vars) :=
  Terms.rec (motive := fun a =>
    r.eqv (r.add (eval r vars a) (a.negatives.eval r vars)) (a.positives.eval r vars))
    (law.add_zero _) (fun sign word tail ih =>
      let w := word.eval r vars
      let n := tail.negatives.eval r vars
      let p := tail.positives.eval r vars
      let t := eval r vars tail
      Bool.rec (motive := fun s =>
        r.eqv (r.add (eval r vars (.cons s word tail)) ((Terms.cons s word tail).negatives.eval r vars))
          ((Terms.cons s word tail).positives.eval r vars))
        (law.trans (law.add_assoc w t n) (law.add_congr (law.refl w) ih))
        (law.trans (law.add_add_add_comm (r.neg w) t w n)
          (law.trans (law.add_congr (law.trans (law.add_comm (r.neg w) w) (law.add_neg w)) ih)
            (law.zero_add p))) sign) a

end Terms

def normalize (e : Expr) : Terms :=
  Expr.rec .nil (.cons .false .nil .nil) (fun i => .cons .false (.cons i .nil) .nil)
    (fun _ _ a b => a.append b) (fun _ a => a.neg) (fun _ _ a b => a.mul b) e

def balance (a b : Expr) : Words :=
  ((normalize a).positives.append (normalize b).negatives).sort

variable {A : Type} {rel : A → A → Prop} (r : CommRingOps A rel) (vars : Variables A)

def eval (e : Expr) : A := Expr.rec r.zero r.one vars
  (fun _ _ a b => r.add a b) (fun _ a => r.neg a) (fun _ _ a b => r.mul a b) e

variable {r vars} (law : r.Laws)
include law

private theorem eval_normalize (e : Expr) :
    r.eqv ((normalize e).eval r vars) (eval r vars e) :=
  Expr.rec (motive := fun e => r.eqv ((normalize e).eval r vars) (eval r vars e))
    (law.refl r.zero) (law.add_zero r.one)
    (fun i => law.trans (law.add_zero (r.mul (vars i) r.one)) (law.mul_one (vars i)))
    (fun a b ha hb => law.trans (Terms.eval_append (vars := vars) law (normalize a) (normalize b))
      (law.add_congr ha hb))
    (fun a ha => law.trans (Terms.eval_neg (vars := vars) law (normalize a)) (law.neg_congr ha))
    (fun a b ha hb => law.trans (Terms.eval_mul (vars := vars) law (normalize a) (normalize b))
      (law.mul_congr ha hb)) e

private theorem eval_balance (a b : Expr) :
    r.eqv ((balance a b).eval r vars)
      (r.add (eval r vars a)
        (r.add ((normalize a).negatives.eval r vars) ((normalize b).negatives.eval r vars))) :=
  let aPos := (normalize a).positives
  let bNeg := (normalize b).negatives
  law.trans (Words.eval_sort (vars := vars) law (aPos.append bNeg))
    (law.trans (Words.eval_append (vars := vars) law aPos bNeg)
      (law.trans (law.add_congr (law.symm (Terms.eval_split (vars := vars) law (normalize a)))
        (law.refl (bNeg.eval r vars)))
        (law.trans (law.add_assoc ((normalize a).eval r vars)
          ((normalize a).negatives.eval r vars) (bNeg.eval r vars))
          (law.add_congr (eval_normalize (vars := vars) law a) (law.refl _)))))

omit law in
/-- A matching pair of lists certifies the identity at every valuation. -/
theorem prove (r : CommRingOps A rel) (law : r.Laws) (vars : Variables A) (a b : Expr)
    (h : Eq (balance a b) (balance b a)) :
    r.eqv (eval r vars a) (eval r vars b) :=
  let x := eval r vars a
  let y := eval r vars b
  let aNeg := (normalize a).negatives.eval r vars
  let bNeg := (normalize b).negatives.eval r vars
  have balanceEq := congrArg (Words.eval r vars) h
  have identity := Eq.subst (fun t => r.eqv ((balance a b).eval r vars) t)
    balanceEq (law.refl ((balance a b).eval r vars))
  have sums := law.trans (law.symm (eval_balance (vars := vars) law a b))
    (law.trans identity (eval_balance (vars := vars) law b a))
  law.add_left_cancel (law.trans (law.add_comm (r.add aNeg bNeg) x)
    (law.trans sums (law.trans (law.add_congr (law.refl y) (law.add_comm bNeg aNeg))
      (law.add_comm y (r.add aNeg bNeg)))))

end Omega.Polynomial
