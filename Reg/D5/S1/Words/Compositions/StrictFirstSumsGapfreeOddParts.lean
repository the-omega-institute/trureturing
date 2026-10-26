import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts

/-! Source-bound audit of the positive-height transpose criterion. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts

abbrev signature : Signature where
  Params := YoungDiagram
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ d h => d.rowLen h < d.rowLen (h - 1)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ d h => ¬ d.rowLen h < d.rowLen (h - 1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (d : YoungDiagram) (h : ℕ), 0 < h →
    (h ∈ d.transpose.rowLens ↔ readout.readout () d h)

private theorem source_bridge : (type_of% (@height_mem_iff)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hyp
  let d := YoungDiagram.ofPartition (Nat.Partition.indiscrete 0)
  have good := height_mem_iff d 1 (by decide)
  have bad := hyp d 1 (by decide)
  change (1 ∈ d.transpose.rowLens ↔ ¬ d.rowLen 1 < d.rowLen (1 - 1)) at bad
  tauto

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let d := (YoungDiagram.ofPartition (Nat.Partition.indiscrete 1)).transpose
  have hd : d.transpose.rowLens = [1] := by simp [d]
  refine ⟨d, 1, 2, ?_⟩
  intro he
  have yes : actual.readout role d 1 :=
    (height_mem_iff d 1 (by decide)).mp (by simp [hd])
  have no : ¬ actual.readout role d 2 := by
    intro h
    have := (height_mem_iff d 2 (by decide)).mpr h
    simpa [hd] using this
  exact no (he ▸ yes)

def familyRegistration : Registration arena (type_of% (@height_mem_iff)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp height_mem_iff, rejected, rejected_law⟩
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
    (@height_mem_iff) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := `D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.height_mem_iff.__information_unit
  realizationName := `Reg.D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.familyRegistration
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
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts
