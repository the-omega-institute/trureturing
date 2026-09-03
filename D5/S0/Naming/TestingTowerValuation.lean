/- GID: D5/S0/Naming/TestingTowerValuation
   generality: G
   mirror-B: D5/B/S0/Naming/TestingTowerValuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tables extend by default and program names are defined exactly when evaluation halts. -/

import D5.S0.Naming.Conservation.TestingTowerMembership
import Mathlib.Computability.Halting

/- Library-search audit trail (2026-09-03):
   * D5 searches for a default table extension, a valuation on `TestingName`,
     and a `Part.toOption`-based program valuation found no matching primitive.
   * Pinned Mathlib supplies `Nat.Partrec.Code.eval`, its denumerable decoder,
     `Part.toOption_isSome`, and `ComputablePred.halting_problem`.
   * GitHub Lean code search for `Nat.Partrec.Code.eval` together with
     `TestingName` returned no result. The definitions below apply the pinned
     evaluator directly rather than introducing a second execution semantics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming.TestingTowerValuation

open D5.S0.Naming.Conservation.TestingTowerMembership

universe u

/-- Extend a finite functional table to a full behavior by using the supplied
default output away from the table's self-selected support. -/
def tableExtension {Output : Type u} (defaultOutput : Output)
    (table : Sigma fun support : Finset Nat => support -> Output) : Nat -> Output :=
  fun input => if h : input ∈ table.1 then table.2 ⟨input, h⟩ else defaultOutput

/-- Run the canonical partial-recursive code represented by a natural-number
program name on the supplied input, then decode a halting result as a behavior. -/
noncomputable def programValuation {X : Type u}
    (decode : Nat -> X) (programInput program : Nat) :
    Option X := by
  letI := Classical.propDecidable
  exact Part.toOption
    ((Nat.Partrec.Code.eval
      (Denumerable.ofNat Nat.Partrec.Code program) programInput).map decode)

/-- The concrete testing-tower assignment: table names denote their default
extensions, while program names use the canonical partial evaluator. -/
noncomputable def testingAssignment {Output : Type u}
    (defaultOutput : Output) (decodeBehavior : Nat -> Nat -> Output)
    (programInput : Nat) :
    TestingName Output -> Option (Nat -> Output)
  | Sum.inl table => some (tableExtension defaultOutput table)
  | Sum.inr program => programValuation decodeBehavior programInput program

/-- A program name is defined exactly when its decoded partial-recursive code
halts on the distinguished input. -/
theorem program_assignment_defined_iff_halts {Output : Type u}
    (defaultOutput : Output) (decodeBehavior : Nat -> Nat -> Output)
    (programInput program : Nat) :
    (testingAssignment defaultOutput decodeBehavior programInput (Sum.inr program)).isSome <->
      (Nat.Partrec.Code.eval
        (Denumerable.ofNat Nat.Partrec.Code program) programInput).Dom := by
  simp [testingAssignment, programValuation]

/-- Definedness of encoded program names is not a computable predicate. -/
theorem program_name_domain_not_computable {Output : Type u}
    (defaultOutput : Output) (decodeBehavior : Nat -> Nat -> Output)
    (programInput : Nat) :
    ¬ ComputablePred (fun code : Nat.Partrec.Code =>
      (testingAssignment defaultOutput decodeBehavior programInput
        (Sum.inr (Nat.Partrec.Code.encodeCode code))).isSome) := by
  intro computableDomain
  apply ComputablePred.halting_problem programInput
  simpa only [program_assignment_defined_iff_halts,
    ← Nat.Partrec.Code.encodeCode_eq, Denumerable.ofNat_encode] using computableDomain

#print axioms program_assignment_defined_iff_halts
#print axioms program_name_domain_not_computable

end D5.S0.Naming.TestingTowerValuation
