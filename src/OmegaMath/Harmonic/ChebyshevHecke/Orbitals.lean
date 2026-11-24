/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Normalized diagonal angular quadrupoles of the five Cartesian real d orbitals.
The model uses the uniform sphere moments of the even monomials of degrees
four and six, all in units of (1/105).
-/

noncomputable section
@[expose] public section

namespace Omega.Chebyshev.Orbitals

inductive Axis where | x | y | z

inductive Orbital where | dz2 | dxz | dyz | dxy | dx2SubY2

def one := Nat.zero.succ
def two := one.succ
def three := two.succ
def four := three.succ
def seven := (four.add two).succ
def fifteen := (seven.add seven).succ
def twentyOne := seven.mul three

def fourthMoment (a b : Axis) : Nat :=
  Axis.rec
    (Axis.rec twentyOne seven seven b)
    (Axis.rec seven twentyOne seven b)
    (Axis.rec seven seven twentyOne b) a

/-- The spherical moment of (x_a^2 x_b^2 x_c^2), scaled by 105. -/
def sixthMoment (a b c : Axis) : Nat :=
  Axis.rec
    (Axis.rec (Axis.rec fifteen three three c)
      (Axis.rec three three one c) (Axis.rec three one three c) b)
    (Axis.rec (Axis.rec three three one c)
      (Axis.rec three fifteen three c) (Axis.rec one three three c) b)
    (Axis.rec (Axis.rec three one three c)
      (Axis.rec one three three c) (Axis.rec three three fifteen c) b) a

/-- Apply a moment functional to the square of the Cartesian orbital polynomial. -/
def densityMoment (o : Orbital) (m : Axis → Axis → Nat) : Int :=
  let xx := Int.ofNat (m .x .x)
  let yy := Int.ofNat (m .y .y)
  let zz := Int.ofNat (m .z .z)
  let xy := Int.ofNat (m .x .y)
  let xz := Int.ofNat (m .x .z)
  let yz := Int.ofNat (m .y .z)
  let i4 := Int.ofNat four
  Orbital.rec
    ((((xx.add yy).add (i4.mul zz)).add (Int.two.mul xy)).sub (i4.mul (xz.add yz)))
    xz yz xy ((xx.add yy).sub (Int.two.mul xy)) o

/-- The expectation of (3x_a^2-1), with the orbital density normalized by its integral. -/
def diagonal (o : Orbital) (a : Axis) : IntRatio :=
  let mass := densityMoment o fourthMoment
  let weighted := densityMoment o (sixthMoment a)
  IntRatio.value (((Int.ofNat three).mul weighted).sub mass) mass.natAbs

def seventh (n : Int) : IntRatio := IntRatio.value n seven

def diagonalIs (o : Orbital) (x y z : Int) : Prop :=
  And (IntRatio.Equivalent (diagonal o .x) (seventh x))
    (And (IntRatio.Equivalent (diagonal o .y) (seventh y))
      (IntRatio.Equivalent (diagonal o .z) (seventh z)))

set_option maxRecDepth 4000 in
theorem diagonal_quadrupoles :
    And (diagonalIs .dz2 Int.two.neg Int.two.neg (Int.ofNat four))
      (And (diagonalIs .dxz Int.two (Int.ofNat four).neg Int.two)
        (And (diagonalIs .dyz (Int.ofNat four).neg Int.two Int.two)
          (And (diagonalIs .dxy Int.two Int.two (Int.ofNat four).neg)
            (diagonalIs .dx2SubY2 Int.two Int.two (Int.ofNat four).neg)))) :=
  And.intro (And.intro Eq.refl (And.intro Eq.refl Eq.refl))
    (And.intro (And.intro Eq.refl (And.intro Eq.refl Eq.refl))
      (And.intro (And.intro Eq.refl (And.intro Eq.refl Eq.refl))
        (And.intro (And.intro Eq.refl (And.intro Eq.refl Eq.refl))
          (And.intro Eq.refl (And.intro Eq.refl Eq.refl)))))

def occupiedFour (a : Axis) : IntRatio :=
  let q := (diagonal .dz2 a).add (diagonal .dxz a)
  let r := (diagonal .dyz a).add (diagonal .dxy a)
  q.add r

def fullShell (a : Axis) : IntRatio := (occupiedFour a).add (diagonal .dx2SubY2 a)

/-- Five spatial orbitals, with two electrons in each orbital. -/
def closedShell (a : Axis) : IntRatio := (IntRatio.ofInt Int.two).mul (fullShell a)

/-- Four doubly occupied spatial orbitals after deleting the (x^2-y^2) orbital. -/
def deletedShell (a : Axis) : IntRatio := (IntRatio.ofInt Int.two).mul (occupiedFour a)

private theorem seventh_add (a b : Int) :
    IntRatio.Equivalent ((seventh a).add (seventh b)) (seventh (a.add b)) :=
  IntRatio.value_add_same a b seven

private theorem sumFour (a : Axis) (p q r s : Int)
    (hp : IntRatio.Equivalent (diagonal .dz2 a) (seventh p))
    (hq : IntRatio.Equivalent (diagonal .dxz a) (seventh q))
    (hr : IntRatio.Equivalent (diagonal .dyz a) (seventh r))
    (hs : IntRatio.Equivalent (diagonal .dxy a) (seventh s)) :
    IntRatio.Equivalent (occupiedFour a) (seventh ((p.add q).add (r.add s))) :=
  (IntRatio.add_congr
    ((IntRatio.add_congr hp hq).trans (seventh_add p q))
    ((IntRatio.add_congr hr hs).trans (seventh_add r s))).trans
      (seventh_add (p.add q) (r.add s))

private theorem fourX : IntRatio.Equivalent (occupiedFour .x) (seventh Int.two.neg) :=
  let h := diagonal_quadrupoles
  sumFour .x _ _ _ _ h.left.left h.right.left.left h.right.right.left.left
    h.right.right.right.left.left

private theorem fourY : IntRatio.Equivalent (occupiedFour .y) (seventh Int.two.neg) :=
  let h := diagonal_quadrupoles
  sumFour .y _ _ _ _ h.left.right.left h.right.left.right.left h.right.right.left.right.left
    h.right.right.right.left.right.left

private theorem fourZ : IntRatio.Equivalent (occupiedFour .z) (seventh (Int.ofNat four)) :=
  let h := diagonal_quadrupoles
  sumFour .z _ _ _ _ h.left.right.right h.right.left.right.right h.right.right.left.right.right
    h.right.right.right.left.right.right

private theorem doubleSeventh {source : IntRatio} {a : Int}
    (h : IntRatio.Equivalent source (seventh a)) :
    IntRatio.Equivalent ((IntRatio.ofInt Int.two).mul source) (seventh (Int.two.mul a)) :=
  (IntRatio.mul_congr (IntRatio.equivalent_refl (IntRatio.ofInt Int.two)) h).trans Eq.refl

theorem full_shell_zero (a : Axis) :
    IntRatio.Equivalent (fullShell a) (IntRatio.ofInt Int.zero) :=
  let h := diagonal_quadrupoles.right.right.right.right
  let zero := IntRatio.value_zero seven (Nat.succ_ne_zero _)
  let cancel := fun (b : Axis) (t u : Int)
    (ht : IntRatio.Equivalent (occupiedFour b) (seventh t))
    (hu : IntRatio.Equivalent (diagonal .dx2SubY2 b) (seventh u))
    (hz : Eq (t.add u) Int.zero) =>
      ((IntRatio.add_congr ht hu).trans (seventh_add t u)).trans
        (Eq.subst (fun v => IntRatio.Equivalent (seventh v) (IntRatio.ofInt Int.zero)) hz.symm zero)
  Axis.rec (motive := fun a => IntRatio.Equivalent (fullShell a) (IntRatio.ofInt Int.zero))
    (cancel .x _ _ fourX h.left Eq.refl) (cancel .y _ _ fourY h.right.left Eq.refl)
    (cancel .z _ _ fourZ h.right.right Eq.refl) a

theorem closed_shell_zero (a : Axis) :
    IntRatio.Equivalent (closedShell a) (IntRatio.ofInt Int.zero) :=
  (IntRatio.mul_congr (IntRatio.equivalent_refl (IntRatio.ofInt Int.two))
    (full_shell_zero a)).trans Eq.refl

theorem deleted_shell_diagonal :
    And (IntRatio.Equivalent (deletedShell .x) (seventh (Int.ofNat four).neg))
      (And (IntRatio.Equivalent (deletedShell .y) (seventh (Int.ofNat four).neg))
        (IntRatio.Equivalent (deletedShell .z) (seventh (Int.ofNat (four.add four))))) :=
  And.intro (doubleSeventh fourX) (And.intro (doubleSeventh fourY) (doubleSeventh fourZ))

theorem deleted_shell_trace_zero :
    IntRatio.Equivalent (((deletedShell .x).add (deletedShell .y)).add (deletedShell .z))
      (IntRatio.ofInt Int.zero) :=
  let h := deleted_shell_diagonal
  have xy := (IntRatio.add_congr h.left h.right.left).trans (seventh_add _ _)
  (IntRatio.add_congr xy h.right.right).trans
    ((seventh_add _ _).trans (IntRatio.value_zero seven (Nat.succ_ne_zero _)))

end Omega.Chebyshev.Orbitals
