module
prelude
public import OmegaMath.Geometry.BargmannGram.Monomial

/-!
Omega original.

Soundness of sparse integer polynomial normalization using only the strict
integer operations. Equality of normalized data is checked by kernel reduction.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram.Polynomial

inductive Terms where
  | zero
  | term (m : Monomial) (c : Int) (tail : Terms)

namespace Terms

def eval (v : Nat → Int) (p : Terms) : Int :=
  Terms.rec Int.zero (fun m c _ r => (c.mul (m.eval v)).add r) p

def cons (m : Monomial) (c : Int) (p : Terms) : Terms :=
  Int.rec (fun n => Nat.rec p (fun k _ => .term m (Int.ofNat k.succ) p) n)
    (fun k => .term m (Int.negSucc k) p) c

private theorem eval_cons (v : Nat → Int) (m : Monomial) (c : Int) (p : Terms) :
    Eq (eval v (cons m c p)) ((c.mul (m.eval v)).add (eval v p)) :=
  Int.rec (motive := fun c => Eq (eval v (cons m c p)) ((c.mul (m.eval v)).add (eval v p)))
    (fun n => Nat.rec (motive := fun n =>
      Eq (eval v (cons m (Int.ofNat n) p)) (((Int.ofNat n).mul (m.eval v)).add (eval v p)))
      ((congrArg (fun c : Int => c.add (eval v p)) (Int.zero_mul (m.eval v))).trans
        (Int.zero_add (eval v p))).symm (fun _ _ => Eq.refl) n)
    (fun _ => Eq.refl) c

def insert (m : Monomial) (c : Int) (p : Terms) : Terms :=
  Terms.rec (cons m c .zero)
    (fun n d rest ih => Ordering.rec
      (cons m c (.term n d rest))
      (cons n (c.add d) rest)
      (.term n d ih) (m.compare n)) p

theorem eval_insert (v : Nat → Int) (m : Monomial) (c : Int) (p : Terms) :
    Eq (eval v (insert m c p)) ((c.mul (m.eval v)).add (eval v p)) :=
  Terms.rec (motive := fun p => Eq (eval v (insert m c p)) ((c.mul (m.eval v)).add (eval v p)))
    (eval_cons v m c .zero)
    (fun n d rest ih =>
      let A := c.mul (m.eval v)
      let B := d.mul (n.eval v)
      let R := eval v rest
      let law := fun cmp => Eq (m.compare n) cmp →
        Eq (eval v (Ordering.rec (motive := fun _ => Terms) (cons m c (.term n d rest))
          (cons n (c.add d) rest) (.term n d (insert m c rest)) cmp)) (A.add (B.add R))
      (Ordering.rec (motive := law)
        (fun _ => eval_cons v m c (.term n d rest))
        (fun e =>
          let h := Monomial.compare_eq m n e
          (eval_cons v n (c.add d) rest).trans
            ((congrArg (fun x : Int => x.add R) (Int.add_mul c d (n.eval v))).trans
              ((Int.add_assoc (c.mul (n.eval v)) B R).trans
                (congrArg (fun x : Monomial => (c.mul (x.eval v)).add (B.add R)) h.symm))))
        (fun _ => (congrArg B.add ih).trans
          ((Int.add_assoc B A R).symm.trans
            ((congrArg (fun x : Int => x.add R) (Int.add_comm B A)).trans (Int.add_assoc A B R))))
        (m.compare n)) Eq.refl) p

def add (p q : Terms) : Terms :=
  Terms.rec q (fun m c _ r => insert m c r) p

theorem eval_add (v : Nat → Int) (p q : Terms) :
    Eq (eval v (add p q)) ((eval v p).add (eval v q)) :=
  Terms.rec (motive := fun p => Eq (eval v (add p q)) ((eval v p).add (eval v q)))
    (Int.zero_add (eval v q)).symm
    (fun m c p ih => (eval_insert v m c (add p q)).trans
      ((congrArg (c.mul (m.eval v)).add ih).trans
        (Int.add_assoc (c.mul (m.eval v)) (eval v p) (eval v q)).symm)) p

def scale (m : Monomial) (c : Int) (p : Terms) : Terms :=
  Terms.rec .zero (fun n d _ r => insert (m.mul n) (c.mul d) r) p

theorem eval_scale (v : Nat → Int) (m : Monomial) (c : Int) (p : Terms) :
    Eq (eval v (scale m c p)) ((c.mul (m.eval v)).mul (eval v p)) :=
  let A := c.mul (m.eval v)
  Terms.rec (motive := fun p => Eq (eval v (scale m c p)) (A.mul (eval v p)))
    (Int.mul_zero A).symm
    (fun n d p ih => (eval_insert v (m.mul n) (c.mul d) (scale m c p)).trans
      ((Eq.map₂ Int.add
        ((congrArg (c.mul d).mul (Monomial.eval_mul v m n)).trans
          (Int.mul_mul_mul_comm c d (m.eval v) (n.eval v))) ih).trans
          (Int.mul_add A (d.mul (n.eval v)) (eval v p)).symm)) p

def mul (p q : Terms) : Terms :=
  Terms.rec .zero (fun m c _ r => add (scale m c q) r) p

theorem eval_mul (v : Nat → Int) (p q : Terms) :
    Eq (eval v (mul p q)) ((eval v p).mul (eval v q)) :=
  Terms.rec (motive := fun p => Eq (eval v (mul p q)) ((eval v p).mul (eval v q)))
    (Int.zero_mul (eval v q)).symm
    (fun m c p ih => (eval_add v (scale m c q) (mul p q)).trans
      ((Eq.map₂ Int.add (eval_scale v m c q) ih).trans
        (Int.add_mul (c.mul (m.eval v)) (eval v p) (eval v q)).symm)) p

end Terms

inductive Expr where
  | var (i : Nat)
  | const (c : Int)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)

namespace Expr

def sub (a b : Expr) : Expr := a.add b.neg
def sq (a : Expr) : Expr := a.mul a

def eval (v : Nat → Int) (p : Expr) : Int :=
  Expr.rec v (fun c => c) (fun _ _ a b => a.add b) (fun _ _ a b => a.mul b)
    (fun _ a => a.neg) p

def normalize (p : Expr) : Terms :=
  Expr.rec (fun i => .term (.factor i .one) Int.one .zero)
    (fun c => Terms.insert .one c .zero)
    (fun _ _ a b => a.add b) (fun _ _ a b => a.mul b)
    (fun _ a => a.scale .one Int.one.neg) p

theorem sound (v : Nat → Int) (p : Expr) : Eq (p.normalize.eval v) (p.eval v) :=
  Expr.rec (motive := fun p => Eq (p.normalize.eval v) (p.eval v))
    (fun i => (Int.add_zero _).trans ((Int.one_mul _).trans (Int.mul_one (v i))))
    (fun c => (Terms.eval_insert v .one c .zero).trans
      ((Int.add_zero _).trans (Int.mul_one c)))
    (fun a b ha hb => (Terms.eval_add v a.normalize b.normalize).trans (Eq.map₂ Int.add ha hb))
    (fun a b ha hb => (Terms.eval_mul v a.normalize b.normalize).trans (Eq.map₂ Int.mul ha hb))
    (fun a ha => (Terms.eval_scale v .one Int.one.neg a.normalize).trans
      ((Eq.map₂ Int.mul (Int.mul_one Int.one.neg) ha).trans
        ((Int.neg_mul Int.one (a.eval v)).trans (congrArg Int.neg (Int.one_mul (a.eval v)))))) p

theorem certify (v : Nat → Int) (a b : Expr) (h : Eq a.normalize b.normalize) :
    Eq (a.eval v) (b.eval v) :=
  (sound v a).symm.trans ((congrArg (Terms.eval v) h).trans (sound v b))

/-- Environment extension for a certificate with consecutive variable indices. -/
def bind (a : Int) (v : Nat → Int) : Nat → Int :=
  fun i => Nat.rec a (fun j _ => v j) i

end Expr
end Omega.Geometry.BargmannGram.Polynomial
