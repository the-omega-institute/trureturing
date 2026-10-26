import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.ColouredOddOccupation
open _root_.D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ r N => partitionCount r N) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ r N => partitionCount r N + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ r N : ℕ,
    Nat.card (ColouredOddFiber (Fin r) N) = readout.readout () r N

private theorem source_bridge :
    (type_of% (@card_colouredFiber)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have good := card_colouredFiber 0 0
  have bad := h 0 0
  change Nat.card (ColouredOddFiber (Fin 0) 0) = partitionCount 0 0 + 1 at bad
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, 1, ?_⟩
  change partitionCount 2 0 ≠ partitionCount 2 1
  rw [(partitionCount_small 2).1, (partitionCount_small 2).2.1]
  decide

def familyRegistration : Registration arena (type_of% (@card_colouredFiber)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp card_colouredFiber, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@card_colouredFiber) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := `D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.card_colouredFiber.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Reg.D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
