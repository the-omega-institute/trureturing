/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.Int

/-!
Omega original.

A checked normalization of the integer polynomial identities used by integer quaternions.
Monomials are sorted lists of variable indices. Insertion in a polynomial merges integer
coefficients of equal monomials and deletes terms whose coefficient is zero.
-/

noncomputable section

@[expose] public section

namespace Omega.Quaternion.Polynomial

/-- Values of the successive variables in an expression. Unlisted variables are zero. -/
inductive Values where
  | nil
  | cons (head : Int) (tail : Values)

def Values.get (v : Values) (n : Nat) : Int :=
  Values.rec (motive := fun _ => Nat → Int) (fun _ => Int.zero)
    (fun a _ rest n => Nat.rec a (fun k _ => rest k) n) v n

inductive Expr where
  | var (index : Nat)
  | one
  | zero
  | neg (a : Expr)
  | add (a b : Expr)
  | mul (a b : Expr)

def Expr.sub (a b : Expr) : Expr := a.add b.neg

def Expr.sq (a : Expr) : Expr := a.mul a

def Expr.double (a : Expr) : Expr := a.add a

def Expr.eval (e : Expr) (v : Values) : Int :=
  Expr.rec (motive := fun _ => Int) v.get Int.one Int.zero
    (fun _ a => a.neg) (fun _ _ a b => a.add b) (fun _ _ a b => a.mul b) e

inductive Factors where
  | nil
  | cons (head : Nat) (tail : Factors)

def Factors.eval (p : Factors) (v : Values) : Int :=
  Factors.rec (motive := fun _ => Int) Int.one (fun n _ r => (v.get n).mul r) p

inductive Compare where
  | less
  | same
  | greater

def compareIndex (a b : Nat) : Compare :=
  Nat.rec (motive := fun _ => Nat → Compare)
    (fun b => Nat.rec .same (fun _ _ => .less) b)
    (fun _ prev b => Nat.rec .greater (fun b _ => prev b) b) a b

def Compare.IsSame (c : Compare) : Prop :=
  Compare.rec False True False c

private theorem index_eq_of_same (a b : Nat) (h : (compareIndex a b).IsSame) : Eq a b :=
  (Nat.rec (motive := fun a => ∀ b, (compareIndex a b).IsSame → Eq a b)
    (fun b => Nat.rec (motive := fun b => (compareIndex Nat.zero b).IsSame → Eq Nat.zero b)
      (fun _ => Eq.refl) (fun _ _ h => False.elim h) b)
    (fun a prev b => Nat.rec (motive := fun b => (compareIndex a.succ b).IsSame → Eq a.succ b)
      (fun h => False.elim h) (fun b _ h => congrArg Nat.succ (prev b h)) b) a) b h

def compareFactors (a b : Factors) : Compare :=
  Factors.rec (motive := fun _ => Factors → Compare)
    (fun b => Factors.rec .same (fun _ _ _ => .less) b)
    (fun i _ prev b => Factors.rec .greater
      (fun j b _ => Compare.rec .less (prev b) .greater (compareIndex i j)) b) a b

private theorem factors_eq_of_same (a b : Factors) (h : (compareFactors a b).IsSame) : Eq a b :=
  (Factors.rec (motive := fun a => ∀ b, (compareFactors a b).IsSame → Eq a b)
    (fun b => Factors.rec (motive := fun b => (compareFactors Factors.nil b).IsSame → Eq Factors.nil b)
      (fun _ => Eq.refl) (fun _ _ _ h => False.elim h) b)
    (fun i a prev b => Factors.rec
      (motive := fun b => (compareFactors (Factors.cons i a) b).IsSame → Eq (Factors.cons i a) b)
      (fun h => False.elim h)
      (fun j b _ hs =>
        let order := compareIndex i j
        (Compare.rec (motive := fun c => (Compare.rec (motive := fun _ => Compare) .less (compareFactors a b) .greater c).IsSame →
          (Eq c order) → Eq (Factors.cons i a) (Factors.cons j b))
          (fun h _ => False.elim h)
          (fun h ij => Eq.map₂ Factors.cons
            (index_eq_of_same i j (Eq.subst Compare.IsSame ij True.intro)) (prev b h))
          (fun h _ => False.elim h) order) hs Eq.refl) b) a) b h

def insertFactor (n : Nat) (p : Factors) : Factors :=
  Factors.rec (motive := fun _ => Factors) (.cons n .nil)
    (fun m p q => Compare.rec (motive := fun _ => Factors)
      (.cons n (.cons m p)) (.cons n (.cons m p)) (.cons m q)
      (compareIndex n m)) p

private theorem eval_insertFactor (n : Nat) (p : Factors) (v : Values) :
    Eq ((insertFactor n p).eval v) ((v.get n).mul (p.eval v)) :=
  Factors.rec (motive := fun p => Eq ((insertFactor n p).eval v) ((v.get n).mul (p.eval v)))
    Eq.refl
    (fun m p ih => Compare.rec
      (motive := fun c => Eq
        ((Compare.rec (motive := fun _ => Factors)
          (.cons n (.cons m p)) (.cons n (.cons m p))
          (.cons m (insertFactor n p)) c).eval v)
        ((v.get n).mul ((v.get m).mul (p.eval v))))
      Eq.refl Eq.refl
      ((congrArg (v.get m).mul ih).trans
        (((Int.mul_assoc (v.get m) (v.get n) (p.eval v)).symm.trans
          (congrArg (fun t : Int => t.mul (p.eval v)) (Int.mul_comm (v.get m) (v.get n)))).trans
          (Int.mul_assoc (v.get n) (v.get m) (p.eval v))))
      (compareIndex n m)) p

def mulFactors (a b : Factors) : Factors :=
  Factors.rec b (fun n _ p => insertFactor n p) a

private theorem eval_mulFactors (a b : Factors) (v : Values) :
    Eq ((mulFactors a b).eval v) ((a.eval v).mul (b.eval v)) :=
  Factors.rec (motive := fun a => Eq ((mulFactors a b).eval v) ((a.eval v).mul (b.eval v)))
    (Int.one_mul (b.eval v)).symm
    (fun n a ih =>
      (eval_insertFactor n (mulFactors a b) v).trans
        ((congrArg (v.get n).mul ih).trans
          (Int.mul_assoc (v.get n) (a.eval v) (b.eval v)).symm)) a

inductive Normal where
  | zero
  | term (factors : Factors) (coefficient : Int) (tail : Normal)

def Normal.eval (p : Normal) (v : Values) : Int :=
  Normal.rec (motive := fun _ => Int) Int.zero
    (fun m a _ rest => (a.mul (m.eval v)).add rest) p

def withCoeff (m : Factors) (a : Int) (p : Normal) : Normal :=
  Int.rec (motive := fun _ => Normal)
    (fun n => Nat.rec (motive := fun _ => Normal) p (fun k _ => .term m (Int.ofNat k.succ) p) n)
    (fun k => .term m (Int.negSucc k) p) a

private theorem eval_withCoeff (m : Factors) (a : Int) (p : Normal) (v : Values) :
    Eq ((withCoeff m a p).eval v) ((a.mul (m.eval v)).add (p.eval v)) :=
  let motive := fun a => Eq ((withCoeff m a p).eval v) ((a.mul (m.eval v)).add (p.eval v))
  Int.rec (motive := motive)
    (fun n => Nat.rec (motive := fun n => motive (Int.ofNat n))
      (((congrArg (fun z : Int => z.add (p.eval v)) (Int.zero_mul (m.eval v))).trans
        (Int.zero_add (p.eval v))).symm)
      (fun _ _ => Eq.refl) n)
    (fun _ => Eq.refl) a

def insert (m : Factors) (a : Int) (p : Normal) : Normal :=
  Normal.rec (motive := fun _ => Normal) (withCoeff m a .zero)
    (fun n b q r => Compare.rec (motive := fun _ => Normal) (withCoeff m a (.term n b q))
      (withCoeff n (a.add b) q) (.term n b r) (compareFactors m n)) p

private theorem eval_insert (m : Factors) (a : Int) (p : Normal) (v : Values) :
    Eq ((insert m a p).eval v) ((a.mul (m.eval v)).add (p.eval v)) :=
  Normal.rec (motive := fun p => Eq ((insert m a p).eval v) ((a.mul (m.eval v)).add (p.eval v)))
    (eval_withCoeff m a .zero v)
    (fun n b q ih =>
      let order := compareFactors m n
      let lhs := fun c => Compare.rec (motive := fun _ => Normal) (withCoeff m a (.term n b q))
        (withCoeff n (a.add b) q) (.term n b (insert m a q)) c
      let A := a.mul (m.eval v)
      let B := b.mul (n.eval v)
      let Q := q.eval v
      (Compare.rec (motive := fun c => Eq c order → Eq ((lhs c).eval v) (A.add (B.add Q)))
        (fun _ => eval_withCoeff m a (.term n b q) v)
        (fun h =>
          have mn := factors_eq_of_same m n (Eq.subst Compare.IsSame h True.intro)
          (eval_withCoeff n (a.add b) q v).trans
            ((congrArg (fun t : Int => t.add Q) (Int.add_mul a b (n.eval v))).trans
              ((Int.add_assoc (a.mul (n.eval v)) B Q).trans
                (congrArg (fun t : Factors => (a.mul (t.eval v)).add (B.add Q)) mn.symm))))
        (fun _ => (congrArg B.add ih).trans
          (((Int.add_assoc B A Q).symm.trans
            (congrArg (fun t : Int => t.add Q) (Int.add_comm B A))).trans
              (Int.add_assoc A B Q))) order) Eq.refl) p

def plus (a b : Normal) : Normal :=
  Normal.rec b (fun m c _ r => insert m c r) a

private theorem eval_plus (a b : Normal) (v : Values) :
    Eq ((plus a b).eval v) ((a.eval v).add (b.eval v)) :=
  Normal.rec (motive := fun a => Eq ((plus a b).eval v) ((a.eval v).add (b.eval v)))
    (Int.zero_add (b.eval v)).symm
    (fun m c p ih => (eval_insert m c (plus p b) v).trans
      ((congrArg (c.mul (m.eval v)).add ih).trans
        (Int.add_assoc (c.mul (m.eval v)) (p.eval v) (b.eval v)).symm)) a

def timesTerm (m : Factors) (a : Int) (p : Normal) : Normal :=
  Normal.rec .zero (fun n b _ q => insert (mulFactors m n) (a.mul b) q) p

private theorem eval_timesTerm (m : Factors) (a : Int) (p : Normal) (v : Values) :
    Eq ((timesTerm m a p).eval v) ((a.mul (m.eval v)).mul (p.eval v)) :=
  Normal.rec (motive := fun p =>
    Eq ((timesTerm m a p).eval v) ((a.mul (m.eval v)).mul (p.eval v)))
    (Int.mul_zero (a.mul (m.eval v))).symm
    (fun n b p ih =>
      (eval_insert (mulFactors m n) (a.mul b) (timesTerm m a p) v).trans
        ((Eq.map₂ Int.add
          ((congrArg (a.mul b).mul (eval_mulFactors m n v)).trans
            (Int.mul_mul_mul_comm a b (m.eval v) (n.eval v))) ih).trans
          (Int.mul_add (a.mul (m.eval v)) (b.mul (n.eval v)) (p.eval v)).symm)) p

def times (a b : Normal) : Normal :=
  Normal.rec .zero (fun m c _ q => plus (timesTerm m c b) q) a

private theorem eval_times (a b : Normal) (v : Values) :
    Eq ((times a b).eval v) ((a.eval v).mul (b.eval v)) :=
  Normal.rec (motive := fun a => Eq ((times a b).eval v) ((a.eval v).mul (b.eval v)))
    (Int.zero_mul (b.eval v)).symm
    (fun m c p ih => (eval_plus (timesTerm m c b) (times p b) v).trans
      ((Eq.map₂ Int.add (eval_timesTerm m c b v) ih).trans
        (Int.add_mul (c.mul (m.eval v)) (p.eval v) (b.eval v)).symm)) a

def negative (a : Normal) : Normal :=
  Normal.rec .zero (fun m c _ q => .term m c.neg q) a

private theorem eval_negative (a : Normal) (v : Values) :
    Eq ((negative a).eval v) (a.eval v).neg :=
  Normal.rec (motive := fun a => Eq ((negative a).eval v) (a.eval v).neg) Eq.refl
    (fun m c _ ih => (Eq.map₂ Int.add (Int.neg_mul c (m.eval v)) ih).trans Int.neg_add.symm) a

def Expr.normalize (e : Expr) : Normal :=
  Expr.rec (fun n => .term (.cons n .nil) Int.one .zero)
    (.term .nil Int.one .zero) .zero
    (fun _ a => negative a) (fun _ _ a b => plus a b) (fun _ _ a b => times a b) e

private theorem eval_normalize (e : Expr) (v : Values) : Eq (e.normalize.eval v) (e.eval v) :=
  Expr.rec (motive := fun e => Eq (e.normalize.eval v) (e.eval v))
    (fun n => (Int.add_zero (Int.one.mul ((v.get n).mul Int.one))).trans
      ((Int.one_mul ((v.get n).mul Int.one)).trans (Int.mul_one (v.get n))))
    Eq.refl Eq.refl
    (fun e ih => (eval_negative e.normalize v).trans (congrArg Int.neg ih))
    (fun e f ih jh => (eval_plus e.normalize f.normalize v).trans (Eq.map₂ Int.add ih jh))
    (fun e f ih jh => (eval_times e.normalize f.normalize v).trans (Eq.map₂ Int.mul ih jh)) e

/-- Lift a kernel reduction of the two normal forms to equality at any integer inputs. -/
theorem Expr.sound (a b : Expr) (v : Values) (h : Eq a.normalize b.normalize) :
    Eq (a.eval v) (b.eval v) :=
  (eval_normalize a v).symm.trans ((congrArg (fun n : Normal => n.eval v) h).trans
    (eval_normalize b v))

/-- Quaternion coordinates over reified integer polynomials. -/
structure Coordinates where
  w : Expr
  x : Expr
  y : Expr
  z : Expr

def Coordinates.variables (n : Nat) : Coordinates :=
  ⟨.var n, .var n.succ, .var n.succ.succ, .var n.succ.succ.succ⟩

def Coordinates.conj (a : Coordinates) : Coordinates :=
  ⟨a.w, a.x.neg, a.y.neg, a.z.neg⟩

def Coordinates.scale (k : Expr) (a : Coordinates) : Coordinates :=
  ⟨k.mul a.w, k.mul a.x, k.mul a.y, k.mul a.z⟩

def Coordinates.scalar (a : Expr) : Coordinates :=
  ⟨a, .zero, .zero, .zero⟩

def Coordinates.mul (a b : Coordinates) : Coordinates :=
  ⟨(((a.w.mul b.w).sub (a.x.mul b.x)).sub (a.y.mul b.y)).sub (a.z.mul b.z),
   (((a.w.mul b.x).add (a.x.mul b.w)).add (a.y.mul b.z)).sub (a.z.mul b.y),
   (((a.w.mul b.y).sub (a.x.mul b.z)).add (a.y.mul b.w)).add (a.z.mul b.x),
   (((a.w.mul b.z).add (a.x.mul b.y)).sub (a.y.mul b.x)).add (a.z.mul b.w)⟩

def Coordinates.dot (a b : Coordinates) : Expr :=
  ((a.w.mul b.w).add (a.x.mul b.x)).add ((a.y.mul b.y).add (a.z.mul b.z))

end Omega.Quaternion.Polynomial
