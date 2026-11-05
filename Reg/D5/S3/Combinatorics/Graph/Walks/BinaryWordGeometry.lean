import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
import Reg.Support.DependentFamily

/-! A full-source audit with the lower-bound distance observation varied. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry

namespace Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry

set_option autoImplicit false

abbrev signature : Signature where
  Params := Word
  State _ := Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ u v => distance u v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ u v : Word,
    (lcp u v <+: u ∧ lcp u v <+: v ∧
      ∀ w : Word, w <+: u → w <+: v → w <+: lcp u v) ∧
    (∀ p : Path u v, r.readout () u v ≤ p.length) ∧
    ∃ p : Path u v, p.length = distance u v ∧ p.Within (max u.length v.length)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h [] []).2.1 (.nil [])
  change 1 ≤ 0 at bad
  exact (by decide : ¬ (1 : ℕ) ≤ 0) bad

def source_registration : Registration arena (type_of% shortest_pop_append) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shortest_pop_append, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨[], [], [true], ?_⟩
    change (0 : ℕ) ≠ 1
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shortest_pop_append) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ u v => distance u v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "arg", "fn", "arg", "body", "fn", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
