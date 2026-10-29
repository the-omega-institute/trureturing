import D5.S3.Observer.Separation.ExecutableCapacityJoin
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin

open _root_.D5.S3.Observer.Separation.FixedTreeCommonExtension
open _root_.D5.S3.Observer.Separation.CapacitySensitiveSupport
open _root_.D5.S3.Observer.Separation.ExecutableCapacityJoin
open _root_.D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open _root_.D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open _root_.D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit


namespace Boundary

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => EmptyCoordinates.answer k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := R.readout () () 0 = false ∧ EmptyCoordinates.answer 1 = true ∧
    minimumPeak (.node () 0 Fin.elim0 : Tree Empty Unit)
      (Set.univ : Set (Empty → Unit)) (fun _ => ()) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact Bool.noConfusion law.1

def evidence : Registration arena (type_of% @_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (by cases other; cases role; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change EmptyCoordinates.answer 0 ≠ EmptyCoordinates.answer 1
    rw [_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result.1,
      _root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result.2.1]
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.Separation.ExecutableCapacityJoin.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Separation.ExecutableCapacityJoin.result.__information_unit
  realizationName := `Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin.Boundary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Separation.ExecutableCapacityJoin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end Boundary
end Reg.D5.S3.Observer.Separation.ExecutableCapacityJoin
