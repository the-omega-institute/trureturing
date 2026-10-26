/- GID: D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary
   mirror-E: none(waiver:structural-proof)
   anchors: []
   utility: none
   digest: Removing the null tuple changes the pp expressibility of ternary disjunction. -/

import D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Boolean pp expressibility and the null tuple -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary

open D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive

/-- The five modes in (left end, right end, middle) order. -/
def A (a : Fin 3 → Bool) : Prop :=
  (a 0 && a 2) = false ∧ (a 1 && a 2) = false

/-- Remove exactly the all-zero tuple. -/
def N (a : Fin 3 → Bool) : Prop :=
  A a ∧ ¬ (a 0 = false ∧ a 1 = false ∧ a 2 = false)

def EQ (a : Fin 2 → Bool) : Prop := a 0 = a 1
def NEQ (a : Fin 2 → Bool) : Prop := a 0 ≠ a 1
def C0 (a : Fin 1 → Bool) : Prop := a 0 = false
def C1 (a : Fin 1 → Bool) : Prop := a 0 = true
def OR3 (a : Fin 3 → Bool) : Prop := (a 0 || a 1 || a 2) = true

/-- Symbols of the larger generating language; no additional relations are implicit. -/
inductive BaseSymbol | five | equal | unequal | zero | one
  deriving DecidableEq

def baseArity : BaseSymbol → Nat
  | .five => 3
  | .equal | .unequal => 2
  | .zero | .one => 1

def baseRelations : (s : BaseSymbol) → (Fin (baseArity s) → Bool) → Prop
  | .five => A
  | .equal => EQ
  | .unequal => NEQ
  | .zero => C0
  | .one => C1

def nArity (_ : Unit) : Nat := 3
def nRelations (_ : Unit) : (Fin 3 → Bool) → Prop := N

/-- Majority is applied coordinatewise to three complete assignments. -/
def majority (a : Fin 3 → Bool) : Bool :=
  (a 0 && a 1) || (a 0 && a 2) || (a 1 && a 2)

/-- Native windows list their bits as (left end, middle, right end). -/
theorem a_window_iff (x y z : Bool) :
    A ![x, y, z] ↔
      ∃ w : D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window,
        D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.bits w = [x, z, y] := by
  cases x <;> cases y <;> cases z <;>
    simp only [A] <;> decide

theorem n_iff_nor (x y z : Bool) :
    N ![x, y, z] ↔ z = !(x || y) := by
  cases x <;> cases y <;> cases z <;>
    simp only [N, A] <;> decide

set_option maxRecDepth 4096 in
private theorem majority_preserves_base :
    ∀ s : BaseSymbol, Preserves majority (baseRelations s) := by
  intro s
  cases s <;> unfold Preserves <;>
    simp only [baseRelations, A, EQ, NEQ, C0, C1, majority] <;> decide

/-- Variables 0,1,2 are x,y,z; variables 3,4,5,6,7 are t,u,v,w,r. -/
def norAtoms : List (Atom nArity (3 + 5)) :=
  [⟨(), ![0, 1, 3]⟩, ⟨(), ![3, 3, 4]⟩, ⟨(), ![4, 2, 5]⟩,
    ⟨(), ![5, 5, 6]⟩, ⟨(), ![7, 6, 7]⟩]

private theorem norAtoms_defines_or3 (a : Fin 3 → Bool) :
    Defines nRelations norAtoms a ↔ OR3 a := by
  change (∃ h : Fin 5 → Bool,
    N ![a 0, a 1, h 0] ∧ N ![h 0, h 0, h 1] ∧
    N ![h 1, a 2, h 2] ∧ N ![h 2, h 2, h 3] ∧ N ![h 4, h 3, h 4] ∧ True) ↔ _
  simp_rw [n_iff_nor]
  constructor
  · rintro ⟨h, ht, hu, hv, hw, hr, _⟩
    unfold OR3
    cases hx : a 0 <;> cases hy : a 1 <;> cases hz : a 2 <;>
      simp_all
  · intro ha
    refine ⟨![!(a 0 || a 1), a 0 || a 1, !(a 0 || a 1 || a 2),
      a 0 || a 1 || a 2, false], ?_⟩
    unfold OR3 at ha
    cases hx : a 0 <;> cases hy : a 1 <;> cases hz : a 2 <;>
      simp_all

/-- Ternary disjunction separates the pp closures with and without the null tuple. -/
theorem result :
    (∀ m : Nat, ∀ atoms : List (Atom baseArity (3 + m)),
      ¬ (∀ a : Fin 3 → Bool, Defines baseRelations atoms a ↔ OR3 a)) ∧
    (∃ m : Nat, ∃ atoms : List (Atom nArity (3 + m)),
      ∀ a : Fin 3 → Bool, Defines nRelations atoms a ↔ OR3 a) := by
  constructor
  · intro m atoms hdefinition
    have hp := polymorphism_preserves_pp baseRelations majority majority_preserves_base atoms
    let rows : Fin 3 → Fin 3 → Bool :=
      ![![true, false, false], ![false, true, false], ![false, false, true]]
    have hrows : ∀ j, Defines baseRelations atoms (rows j) := by
      intro j
      apply (hdefinition (rows j)).mpr
      fin_cases j <;> simp [rows, OR3]
    have hout := (hdefinition _).mp (hp rows hrows)
    change false = true at hout
    cases hout
  · exact ⟨5, norAtoms, norAtoms_defines_or3⟩

end D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
