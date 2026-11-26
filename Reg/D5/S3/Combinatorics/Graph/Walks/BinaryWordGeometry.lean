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

private abbrev nilSignature : Signature where
  Params := Unit
  State _ := Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def nilDistance : Realization nilSignature :=
  realize nilSignature (fun _ _ v => distance [] v) (fun e => nomatch e)

private def nilOne : Realization nilSignature :=
  realize nilSignature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev nilArena : Arena where
  signature := nilSignature
  Law r := ∀ v : Word, r.readout () () v = v.length

private theorem nilOne_invalid : ¬ nilArena.Law nilOne := by
  intro h
  have bad := h []
  change (1 : ℕ) = 0 at bad
  exact Nat.one_ne_zero bad

private theorem nilDistance_varies :
    nilDistance.readout () () [] ≠ nilDistance.readout () () [true] := by decide

def nilDistanceEvidence : Registration nilArena (type_of% distance_nil_left) where
  actual := nilDistance
  bridge := Iff.rfl
  variation := ⟨distance_nil_left, nilOne, nilOne_invalid⟩
  sensitivity := ⟨fun i => ⟨nilOne, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, nilOne_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨(), [], [true], nilDistance_varies⟩

def nilDistanceRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@distance_nil_left) (Realization nilSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.distance_nil_left
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.nilDistanceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨nilArena⟩
  objectArena := .source ⟨nilArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nilArena ⟨nilDistanceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nilSignature (fun _ _ v => distance [] v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev consArena : Arena where
  signature := signature
  Law r := ∀ (a b : Bool) (u v : Word),
    distance (a :: u) (b :: v) =
      if a = b then r.readout () u v else (a :: u).length + (b :: v).length

private theorem consOne_invalid : ¬ consArena.Law rejected := by
  intro h
  have bad := h false false [] []
  change (0 : ℕ) = 1 at bad
  exact Nat.zero_ne_one bad

def consDistanceEvidence : Registration consArena (type_of% distance_cons) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨distance_cons, rejected, consOne_invalid⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, consOne_invalid⟩, fun e => nomatch e⟩
  dependence := source_registration.dependence

def consDistanceRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@distance_cons) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.distance_cons
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.consDistanceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨consArena⟩
  objectArena := .source ⟨consArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source consArena ⟨consDistanceEvidence⟩
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
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
