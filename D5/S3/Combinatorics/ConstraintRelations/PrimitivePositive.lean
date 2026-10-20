/- GID: D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ConstraintRelations/PrimitivePositive
   mirror-E: none(waiver:structural-proof)
   anchors: []
   utility: none
   digest: Generator-preserving operations preserve finite existential conjunctions. -/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic

/-! # Primitive-positive definitions and polymorphism preservation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive

universe u v

/-- A relation symbol and an arbitrary tuple of variable indices. Repeated indices are legal. -/
structure Atom {S : Type v} (arity : S → Nat) (variableCount : Nat) where
  symbol : S
  arguments : Fin (arity symbol) → Fin variableCount

/-- Interpret one atom in a complete variable assignment. -/
def Atom.Holds {D : Type u} {S : Type v} {arity : S → Nat} {n : Nat}
    (relations : (s : S) → (Fin (arity s) → D) → Prop)
    (atom : Atom arity n) (assignment : Fin n → D) : Prop :=
  relations atom.symbol (fun i => assignment (atom.arguments i))

/-- Empty conjunction is true; a nonempty conjunction interprets its head and its tail. -/
def HoldsAll {D : Type u} {S : Type v} {arity : S → Nat} {n : Nat}
    (relations : (s : S) → (Fin (arity s) → D) → Prop) :
    List (Atom arity n) → (Fin n → D) → Prop
  | [], _ => True
  | atom :: atoms, assignment => atom.Holds relations assignment ∧
      HoldsAll relations atoms assignment

/-- The first n variables are free and the last m are existentially quantified. -/
def Defines {D : Type u} {S : Type v} {arity : S → Nat} {n m : Nat}
    (relations : (s : S) → (Fin (arity s) → D) → Prop)
    (atoms : List (Atom arity (n + m))) (a : Fin n → D) : Prop :=
  ∃ h : Fin m → D, HoldsAll relations atoms (Fin.append a h)

/-- Coordinatewise preservation, including zero-ary operations and relations. -/
def Preserves {D : Type u} {k n : Nat} (operation : (Fin k → D) → D)
    (relation : (Fin n → D) → Prop) : Prop :=
  ∀ rows : Fin k → Fin n → D, (∀ j, relation (rows j)) →
    relation (fun i => operation (fun j => rows j i))

private theorem holdsAll_preserved {D : Type u} {S : Type v} {arity : S → Nat}
    {k n : Nat} (relations : (s : S) → (Fin (arity s) → D) → Prop)
    (operation : (Fin k → D) → D)
    (generators : ∀ s, Preserves operation (relations s))
    (atoms : List (Atom arity n)) : Preserves operation (HoldsAll relations atoms) := by
  induction atoms with
  | nil => intro rows h; trivial
  | cons atom atoms ih =>
      intro rows h
      constructor
      · exact generators atom.symbol (fun j i => rows j (atom.arguments i))
          (fun j => (h j).1)
      · exact ih rows (fun j => (h j).2)

/-- Polymorphisms commute with variable substitution, conjunction and existential hiding. -/
theorem polymorphism_preserves_pp {D : Type u} {S : Type v} {arity : S → Nat}
    {k n m : Nat} (relations : (s : S) → (Fin (arity s) → D) → Prop)
    (operation : (Fin k → D) → D)
    (generators : ∀ s, Preserves operation (relations s))
    (atoms : List (Atom arity (n + m))) : Preserves operation (Defines relations atoms) := by
  classical
  intro rows hrows
  choose witnesses hwitnesses using hrows
  refine ⟨fun i => operation (fun j => witnesses j i), ?_⟩
  have h := holdsAll_preserved relations operation generators atoms
    (fun j => Fin.append (rows j) (witnesses j)) hwitnesses
  convert h using 1
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

end D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
