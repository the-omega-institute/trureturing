/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.IntRatio

/-!
Omega original.

The six norm-five generators, their squared scalar overlap, and the
integer symmetric powers of their defining Gaussian-integer matrices.
-/

noncomputable section
@[expose] public section

namespace Omega.Chebyshev.S5

def n1 := Nat.zero.succ
def n2 := n1.succ
def n3 := n2.succ
def n4 := n3.succ
def n5 := n4.succ
def n6 := n5.succ

def i4 := Int.ofNat n4
def i5 := Int.ofNat n5
def i6 := Int.ofNat n6

structure Quaternion where
  w : Int
  x : Int
  y : Int
  z : Int

inductive Generator where | xPlus | xMinus | yPlus | yMinus | zPlus | zMinus

def Generator.coordinates (g : Generator) : Quaternion :=
  let p := Int.two
  let m := p.neg
  let o := Int.zero
  let i := Int.one
  Generator.rec ⟨i, p, o, o⟩ ⟨i, m, o, o⟩ ⟨i, o, p, o⟩ ⟨i, o, m, o⟩
    ⟨i, o, o, p⟩ ⟨i, o, o, m⟩ g

def Quaternion.normSq (q : Quaternion) : Int :=
  ((q.w.square.add q.x.square).add q.y.square).add q.z.square

def Quaternion.kappa (q : Quaternion) : IntRatio :=
  IntRatio.value q.w.square q.normSq.natAbs

theorem norm_five (g : Generator) : Eq g.coordinates.normSq i5 :=
  Generator.rec (motive := fun g => Eq g.coordinates.normSq i5)
    Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl g

theorem kappa_one_fifth (g : Generator) :
    Eq g.coordinates.kappa (IntRatio.value Int.one n5) :=
  Generator.rec (motive := fun g => Eq g.coordinates.kappa (IntRatio.value Int.one n5))
    Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl g

structure Gaussian where
  re : Int
  im : Int

namespace Gaussian

def ofInt (a : Int) : Gaussian := ⟨a, Int.zero⟩

def add (a b : Gaussian) : Gaussian := ⟨a.re.add b.re, a.im.add b.im⟩

def mul (a b : Gaussian) : Gaussian :=
  ⟨(a.re.mul b.re).sub (a.im.mul b.im), (a.re.mul b.im).add (a.im.mul b.re)⟩

end Gaussian

structure DefiningMatrix where
  a : Gaussian
  b : Gaussian
  c : Gaussian
  d : Gaussian

/-- The usual two-dimensional complex representation, before normalizing the quaternion. -/
def Quaternion.definingMatrix (q : Quaternion) : DefiningMatrix :=
  ⟨⟨q.w, q.x⟩, ⟨q.y, q.z⟩, ⟨q.y.neg, q.z⟩, ⟨q.w, q.x.neg⟩⟩

def DefiningMatrix.trace (m : DefiningMatrix) : Gaussian := m.a.add m.d

def DefiningMatrix.determinant (m : DefiningMatrix) : Gaussian :=
  let x := m.a.mul m.d
  let y := m.b.mul m.c
  ⟨x.re.sub y.re, x.im.sub y.im⟩

/-- Each generating matrix has characteristic polynomial (z^2-2z+5). -/
theorem defining_trace_det (g : Generator) :
    And (Eq g.coordinates.definingMatrix.trace (Gaussian.ofInt Int.two))
      (Eq g.coordinates.definingMatrix.determinant (Gaussian.ofInt i5)) :=
  Generator.rec (motive := fun g =>
    And (Eq g.coordinates.definingMatrix.trace (Gaussian.ofInt Int.two))
      (Eq g.coordinates.definingMatrix.determinant (Gaussian.ofInt i5)))
    (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl)
    (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl) (And.intro Eq.refl Eq.refl) g

/-- Coefficient array of a polynomial in the ratio of the second variable to the first. -/
def Polynomial := Nat → Gaussian

def Polynomial.one : Polynomial :=
  fun i => Nat.rec (Gaussian.ofInt Int.one) (fun _ _ => Gaussian.ofInt Int.zero) i

/-- Multiply by a linear form in homogeneous coordinates. -/
def Polynomial.linearMul (a b : Gaussian) (p : Polynomial) : Polynomial :=
  fun i => Nat.rec (a.mul (p .zero)) (fun k _ => (a.mul (p k.succ)).add (b.mul (p k))) i

/-- Coefficients in the image of a monomial under the defining complex representation. -/
def Quaternion.symmetricPower (q : Quaternion) (left right row : Nat) : Gaussian :=
  let m := q.definingMatrix
  let first := Polynomial.linearMul m.a m.c
  let second := Polynomial.linearMul m.b m.d
  let firstPower : Polynomial := Nat.rec Polynomial.one (fun _ p => first p) left
  (Nat.rec (motive := fun _ => Polynomial) firstPower (fun _ p => second p) right) row

/-- A coefficient of the six-generator sum on degree n = left + right. -/
def coefficient (left right row : Nat) : Gaussian :=
  let c := fun (g : Generator) => g.coordinates.symmetricPower left right row
  (((c .xPlus).add (c .xMinus)).add ((c .yPlus).add (c .yMinus))).add
    ((c .zPlus).add (c .zMinus))

end Omega.Chebyshev.S5
