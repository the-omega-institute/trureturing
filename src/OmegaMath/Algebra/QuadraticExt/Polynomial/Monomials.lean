module
prelude
public import OmegaMath.Algebra.QuadraticExt.Ring

/-!
Omega original.

Ordered monomials for checking polynomial identities in a commutative ring.
-/

noncomputable section
@[expose] public section

namespace Omega.Polynomial

def Variables (A : Type) : Type := Nat → A

namespace Variables
def nil {A : Type} {rel : A → A → Prop} (r : CommRingOps A rel) : Variables A :=
  fun _ => r.zero

def cons {A : Type} (a : A) (vars : Variables A) : Variables A :=
  fun i => Nat.rec a (fun j _ => vars j) i
end Variables

inductive Comparison where
  | less
  | equal
  | greater

def compareNat (a b : Nat) : Comparison :=
  Nat.rec (motive := fun _ => Nat → Comparison)
    (fun b => Nat.rec .equal (fun _ _ => .less) b)
    (fun _ prev b => Nat.rec .greater (fun j _ => prev j) b) a b

inductive Word where
  | nil
  | cons (index : Nat) (rest : Word)

namespace Word

def le (a b : Word) : Bool :=
  Word.rec (motive := fun _ => Word → Bool) (fun _ => .true)
    (fun i _ prev b => Word.rec (motive := fun _ => Bool) .false
      (fun j tail _ => Comparison.rec .true (prev tail) .false (compareNat i j)) b) a b

def insert (i : Nat) (w : Word) : Word :=
  Word.rec (.cons i .nil) (fun j tail prev =>
    Comparison.rec (.cons i (.cons j tail)) (.cons i (.cons j tail))
      (.cons j prev) (compareNat i j)) w

def mul (a b : Word) : Word :=
  Word.rec b (fun i _ prev => prev.insert i) a

variable {A : Type} {rel : A → A → Prop} (r : CommRingOps A rel)
  (vars : Variables A)

def eval (w : Word) : A := Word.rec r.one (fun i _ tail => r.mul (vars i) tail) w

variable {r vars} (law : r.Laws)
include law

theorem eval_insert (i : Nat) (w : Word) :
    r.eqv (eval r vars (w.insert i)) (r.mul (vars i) (eval r vars w)) :=
  Word.rec (motive := fun w => r.eqv (eval r vars (w.insert i))
    (r.mul (vars i) (eval r vars w)))
    (law.refl _) (fun j tail ih =>
      let insertAt (choice : Comparison) : Word :=
        Comparison.rec (motive := fun _ => Word) (.cons i (.cons j tail)) (.cons i (.cons j tail))
          (.cons j (tail.insert i)) choice
      Comparison.rec (motive := fun choice =>
        r.eqv (eval r vars (insertAt choice)) (r.mul (vars i) (eval r vars (.cons j tail))))
        (law.refl (r.mul (vars i) (eval r vars (.cons j tail))))
        (law.refl (r.mul (vars i) (eval r vars (.cons j tail))))
        (law.trans (law.mul_congr (law.refl (vars j)) ih)
          (law.trans (law.symm (law.mul_assoc (vars j) (vars i) (eval r vars tail)))
            (law.trans (law.mul_congr (law.mul_comm (vars j) (vars i))
              (law.refl (eval r vars tail)))
              (law.mul_assoc (vars i) (vars j) (eval r vars tail)))))
        (compareNat i j)) w

theorem eval_mul (a b : Word) :
    r.eqv (eval r vars (a.mul b)) (r.mul (eval r vars a) (eval r vars b)) :=
  Word.rec (motive := fun a =>
    r.eqv (eval r vars (a.mul b)) (r.mul (eval r vars a) (eval r vars b)))
    (law.symm (law.one_mul _))
    (fun i tail ih => law.trans (eval_insert (vars := vars) law i (tail.mul b))
      (law.trans (law.mul_congr (law.refl (vars i)) ih)
        (law.symm (law.mul_assoc (vars i) (eval r vars tail) (eval r vars b))))) a

end Word

inductive Words where
  | nil
  | cons (word : Word) (rest : Words)

namespace Words

def insert (w : Word) (ws : Words) : Words :=
  Words.rec (.cons w .nil)
    (fun k tail prev => Bool.rec (.cons k prev) (.cons w (.cons k tail)) (w.le k)) ws

def append (ws ks : Words) : Words := Words.rec ks (fun w _ prev => .cons w prev) ws

def sort (ws : Words) : Words := Words.rec .nil (fun w _ prev => prev.insert w) ws

variable {A : Type} {rel : A → A → Prop} (r : CommRingOps A rel)
  (vars : Variables A)

def eval (ws : Words) : A :=
  Words.rec r.zero (fun w _ tail => r.add (w.eval r vars) tail) ws

variable {r vars} (law : r.Laws)
include law

theorem eval_append (ws ks : Words) :
    r.eqv (eval r vars (ws.append ks)) (r.add (eval r vars ws) (eval r vars ks)) :=
  Words.rec (motive := fun ws =>
    r.eqv (eval r vars (ws.append ks)) (r.add (eval r vars ws) (eval r vars ks)))
    (law.symm (law.zero_add _))
    (fun w tail ih => law.trans (law.add_congr (law.refl (w.eval r vars)) ih)
      (law.symm (law.add_assoc (w.eval r vars) (eval r vars tail) (eval r vars ks)))) ws

theorem eval_insert (w : Word) (ws : Words) :
    r.eqv (eval r vars (ws.insert w)) (r.add (w.eval r vars) (eval r vars ws)) :=
  Words.rec (motive := fun ws =>
    r.eqv (eval r vars (ws.insert w)) (r.add (w.eval r vars) (eval r vars ws)))
    (law.refl _) (fun k tail ih =>
      let insertAt (choice : Bool) : Words :=
        Bool.rec (motive := fun _ => Words) (.cons k (tail.insert w)) (.cons w (.cons k tail)) choice
      Bool.rec (motive := fun choice => r.eqv (eval r vars (insertAt choice))
        (r.add (w.eval r vars) (eval r vars (.cons k tail))))
        (law.trans (law.add_congr (law.refl (k.eval r vars)) ih)
          (law.trans (law.symm (law.add_assoc (k.eval r vars) (w.eval r vars) (eval r vars tail)))
            (law.trans (law.add_congr (law.add_comm (k.eval r vars) (w.eval r vars))
              (law.refl (eval r vars tail)))
              (law.add_assoc (w.eval r vars) (k.eval r vars) (eval r vars tail)))))
        (law.refl _) (w.le k)) ws

theorem eval_sort (ws : Words) : r.eqv (eval r vars ws.sort) (eval r vars ws) :=
  Words.rec (motive := fun ws => r.eqv (eval r vars ws.sort) (eval r vars ws))
    (law.refl _) (fun w tail ih => law.trans (eval_insert (vars := vars) law w tail.sort)
      (law.add_congr (law.refl (w.eval r vars)) ih)) ws

end Words
end Omega.Polynomial
