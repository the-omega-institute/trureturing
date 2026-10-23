/- GID: D5/S0/Computability/PresburgerSyntax
   generality: G
   mirror-B: D5/B/S0/Computability/PresburgerSyntax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executable integer Presburger syntax with exact semantics. -/

/- Source: VladimirReshetnikov/ProveIt, ec9ab2ffd49f8861022d6f3d4c30205545a3386d,
   PresburgerArithmetic/Syntax.lean.
   Original SHA256: 62d5f20d134a3ce475d29e16bc69160ed9ae4263414d718f62e533c65adeac88.
   License: MIT-0; docs/reports/presburger-suppliers/ProveIt-LICENSE.txt. -/

import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

namespace PresburgerArithmetic

/-! A small, executable syntax for first-order Presburger arithmetic over `ℤ`.

An affine expression is stored as a constant and a (possibly short) list of
coefficients.  Missing coefficients are zero.  Quantifiers use de Bruijn
indices: the newly bound integer is consed onto the valuation.
-/

structure Affine where
  constant : Int
  coeffs : List Int
  deriving DecidableEq, Repr

namespace Affine

def dot : List Int → List Int → Int
  | a :: as, x :: xs => a * x + dot as xs
  | _, _ => 0

def eval (t : Affine) (xs : List Int) : Int :=
  t.constant + dot t.coeffs xs

def coeffAdd : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: coeffAdd xs ys

def neg (t : Affine) : Affine :=
  ⟨-t.constant, t.coeffs.map (-·)⟩

def add (s t : Affine) : Affine :=
  ⟨s.constant + t.constant, coeffAdd s.coeffs t.coeffs⟩

def scale (k : Int) (t : Affine) : Affine :=
  ⟨k * t.constant, t.coeffs.map (k * ·)⟩

def head (t : Affine) : Int := t.coeffs.head?.getD 0
def tail (t : Affine) : Affine := ⟨t.constant, t.coeffs.drop 1⟩

def consCoeff (a : Int) (t : Affine) : Affine :=
  ⟨t.constant, a :: t.coeffs⟩

def const (k : Int) : Affine := ⟨k, []⟩

@[simp] theorem head_consCoeff (a : Int) (t : Affine) :
    (consCoeff a t).head = a := by simp [head, consCoeff]

@[simp] theorem tail_consCoeff (a : Int) (t : Affine) :
    (consCoeff a t).tail = t := by simp [tail, consCoeff]

@[simp] theorem dot_nil_right (as : List Int) : dot as [] = 0 := by cases as <;> rfl

theorem dot_map_neg (as xs : List Int) : dot (as.map (-·)) xs = -dot as xs := by
  induction as generalizing xs with
  | nil => simp [dot]
  | cons a as ih =>
      cases xs with
      | nil => simp
      | cons x xs => simp [dot, ih]; ring

theorem dot_map_mul (k : Int) (as xs : List Int) :
    dot (as.map (k * ·)) xs = k * dot as xs := by
  induction as generalizing xs with
  | nil => simp [dot]
  | cons a as ih =>
      cases xs with
      | nil => simp
      | cons x xs => simp [dot, ih]; ring

theorem dot_coeffAdd (as bs xs : List Int) :
    dot (coeffAdd as bs) xs = dot as xs + dot bs xs := by
  induction as generalizing bs xs with
  | nil => simp [coeffAdd, dot]
  | cons a as ih =>
      cases bs with
      | nil => simp [coeffAdd, dot]
      | cons b bs =>
          cases xs with
          | nil => simp
          | cons x xs => simp [coeffAdd, dot, ih]; ring

@[simp] theorem eval_neg (t : Affine) (xs : List Int) : t.neg.eval xs = -t.eval xs := by
  simp [neg, eval, dot_map_neg]
  ring

@[simp] theorem eval_add (s t : Affine) (xs : List Int) :
    (s.add t).eval xs = s.eval xs + t.eval xs := by
  simp [add, eval, dot_coeffAdd]; ring

@[simp] theorem eval_scale (k : Int) (t : Affine) (xs : List Int) :
    (t.scale k).eval xs = k * t.eval xs := by
  simp [scale, eval, dot_map_mul]; ring

@[simp] theorem eval_const (k : Int) (xs : List Int) : (const k).eval xs = k := by
  simp [const, eval, dot]

@[simp] theorem eval_consCoeff (a : Int) (t : Affine) (x : Int) (xs : List Int) :
    (consCoeff a t).eval (x :: xs) = a * x + t.eval xs := by
  simp [consCoeff, eval, dot]; ring

end Affine

inductive Atom where
  | le (t : Affine)                    -- `0 ≤ t`
  | dvd (modulus : Nat) (positive : 0 < modulus) (t : Affine)
  | ndvd (modulus : Nat) (positive : 0 < modulus) (t : Affine)
  deriving Repr

namespace Atom

def eval : Atom → List Int → Bool
  | .le t, xs => decide (0 ≤ t.eval xs)
  | .dvd d _ t, xs => decide ((d : Int) ∣ t.eval xs)
  | .ndvd d _ t, xs => decide (¬(d : Int) ∣ t.eval xs)

def affine : Atom → Affine
  | .le t | .dvd _ _ t | .ndvd _ _ t => t

def mapAffine (f : Affine → Affine) : Atom → Atom
  | .le t => .le (f t)
  | .dvd d hd t => .dvd d hd (f t)
  | .ndvd d hd t => .ndvd d hd (f t)

end Atom

inductive QF where
  | truth
  | falsity
  | atom (a : Atom)
  | and (p q : QF)
  | or (p q : QF)
  | not (p : QF)
  deriving Repr

namespace QF

def eval : QF → List Int → Bool
  | .truth, _ => true
  | .falsity, _ => false
  | .atom a, xs => a.eval xs
  | .and p q, xs => p.eval xs && q.eval xs
  | .or p q, xs => p.eval xs || q.eval xs
  | .not p, xs => !(p.eval xs)

def conjunction : List Atom → QF
  | [] => .truth
  | a :: as => .and (.atom a) (conjunction as)

def disjunction : List QF → QF
  | [] => .falsity
  | p :: ps => .or p (disjunction ps)

def conjList : List QF → QF
  | [] => .truth
  | p :: ps => .and p (conjList ps)

@[simp] theorem eval_conjunction (as : List Atom) (xs : List Int) :
    (conjunction as).eval xs = as.all fun a => a.eval xs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [conjunction, eval, ih]

@[simp] theorem eval_disjunction (ps : List QF) (xs : List Int) :
    (disjunction ps).eval xs = ps.any fun p => p.eval xs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [disjunction, eval, ih]

@[simp] theorem eval_conjList (ps : List QF) (xs : List Int) :
    (conjList ps).eval xs = ps.all fun p => p.eval xs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [conjList, eval, ih]

end QF

inductive Formula where
  | qf (p : QF)
  | and (p q : Formula)
  | or (p q : Formula)
  | not (p : Formula)
  | exists_ (p : Formula)
  deriving Repr

namespace Formula

def holds : Formula → List Int → Prop
  | .qf p, xs => p.eval xs = true
  | .and p q, xs => p.holds xs ∧ q.holds xs
  | .or p q, xs => p.holds xs ∨ q.holds xs
  | .not p, xs => ¬p.holds xs
  | .exists_ p, xs => ∃ x : Int, p.holds (x :: xs)

def all (p : Formula) : Formula := .not (.exists_ (.not p))

abbrev Sentence := Formula

end Formula

end PresburgerArithmetic
