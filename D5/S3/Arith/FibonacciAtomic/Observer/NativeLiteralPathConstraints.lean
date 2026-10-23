/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite native constraints for literal navigation on one original source. -/

import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)

/-- Labels, iterates of the one original source, and bound auxiliary trees. -/
abbrev Atom := Bool ⊕ (Nat ⊕ Nat)

abbrev Term := FreeMagma Atom

def label (b : Bool) : Term := .of (.inl b)
def original (i : Nat) : Term := .of (.inr (.inl i))
def auxiliary (i : Nat) : Term := .of (.inr (.inr i))

/-- Epochs are interpretation parameters, not literal constants in the terms. -/
def value (u : Source) (e : Nat → Nat) (x : Nat → Source) : Term → Source
  | .of (.inl b) => .of b
  | .of (.inr (.inl i)) => substitution^[e i] u
  | .of (.inr (.inr i)) => x i
  | .mul l r => .mul (value u e x l) (value u e x r)

def push (t : Source) (x : Nat → Source) : Nat → Source
  | 0 => t
  | n+1 => x n

/-- Opening a tree binder shifts only auxiliary names, never the source. -/
def lift : Term → Term
  | .of (.inr (.inr i)) => auxiliary (i+1)
  | .of a => .of a
  | .mul l r => .mul (lift l) (lift r)

private theorem value_lift (u : Source) (e : Nat → Nat) (x : Nat → Source)
    (t : Source) (V : Term) : value u e (push t x) (lift V) = value u e x V := by
  induction V with
  | of a => cases a with
    | inl b => rfl
    | inr a => cases a <;> rfl
  | mul l r hl hr => simp only [lift, value, hl, hr]

/-- A finite equality/Boolean/existential grammar with no readout predicate. -/
inductive Formula where
  | bottom
  | equal : Term → Term → Formula
  | both : Formula → Formula → Formula
  | either : Formula → Formula → Formula
  | treeExists : Formula → Formula

def Formula.Holds (u : Source) (e : Nat → Nat) (x : Nat → Source) : Formula → Prop
  | .bottom => False
  | .equal A B => value u e x A = value u e x B
  | .both A B => A.Holds u e x ∧ B.Holds u e x
  | .either A B => A.Holds u e x ∨ B.Holds u e x
  | .treeExists A => ∃ t : Source, A.Holds u e (push t x)

/-- A reached pair binds its actual ordered children before continuing. -/
def pairStep (V : Term) (b : Bool) (F : Term → Formula) : Formula :=
  .treeExists (.treeExists (.both
    (.equal (lift (lift V)) (.mul (auxiliary 1) (auxiliary 0)))
    (F (auxiliary (if b then 0 else 1)))))

/-- At a missing address, a strict-prefix leaf is an alternative to descent.
The empty address has no absence alternative. All addresses are literal words. -/
def compile : Address → Reply → Term → Formula
  | [], .alpha, V => .equal V (label true)
  | [], .beta, V => .equal V (label false)
  | [], .branch, V => .treeExists (.treeExists
      (.equal (lift (lift V)) (.mul (auxiliary 1) (auxiliary 0))))
  | [], .absent, _ => .bottom
  | b :: p, .absent, V => .either
      (.either (.equal V (label true)) (.equal V (label false)))
      (pairStep V b (compile p .absent))
  | b :: p, y, V => pairStep V b (compile p y)

/-- The constructor constraints preserve the exact tree being queried, including
every sibling witness and the strict-prefix alternatives for absence. -/
theorem compile_exact (u : Source) (e : Nat → Nat) (x : Nat → Source)
    (p : Address) (y : Reply) (V : Term) :
    (compile p y V).Holds u e x ↔ readout p (value u e x V) = y := by
  have pair_eq (a b c d : Source) :
      FreeMagma.mul a b = .mul c d ↔ a = c ∧ b = d := by
    constructor
    · intro h; injection h with h₁ h₂; exact ⟨h₁, h₂⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have leaf_eq (a b : Bool) : (FreeMagma.of a : Source) = .of b ↔ a = b := by
    constructor
    · intro h; injection h
    · rintro rfl; rfl
  induction p generalizing x V y with
  | nil =>
      cases y <;>
        simp only [compile, Formula.Holds, value_lift, value, auxiliary, label, push]
      all_goals cases value u e x V with
      | of b => cases b <;> simp [readout, leaf_eq]
      | mul l r => simp [readout, -FreeMagma.mul_eq, pair_eq]
  | cons b p ih =>
      have step (y : Reply) :
          (pairStep V b (compile p y)).Holds u e x ↔
          ∃ l r : Source, value u e x V = .mul l r ∧
            readout p (if b then r else l) = y := by
        simp only [pairStep, Formula.Holds, value_lift, value, auxiliary, push, ih]
        cases b <;> rfl
      cases y <;> simp only [compile, step, Formula.Holds, value, label]
      all_goals cases value u e x V with
      | of a => cases a <;> simp [readout, leaf_eq]
      | mul l r => cases b <;> simp [readout, -FreeMagma.mul_eq, pair_eq]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeLiteralPathConstraints
