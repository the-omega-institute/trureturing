import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

set_option autoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

namespace Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

abbrev signature : Signature where
  Params := Type
  State ι := (ι × ℕ) →₀ ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output ι _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ι d => colouredEnergy ι d ≤ 2 * integerEnergy ι d) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (ι : Type) (d : (ι × ℕ) →₀ ℕ),
    a.readout () ι d ↔ colouredEnergy ι d ≤ 2 * integerEnergy ι d

private theorem source_bridge :
    (type_of% (@oddEnergy_le_twice_integerEnergy)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h Empty (0 : (Empty × ℕ) →₀ ℕ)).mp
  exact Nat.not_succ_le_zero 1 (by simpa [integerEnergy, colouredEnergy] using hh)

def familyRegistration : Registration arena (type_of% (@oddEnergy_le_twice_integerEnergy)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp oddEnergy_le_twice_integerEnergy, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    intro ι
    refine ⟨ι, 0, ?_⟩
    intro h
    exact (h.mp (by simp [actual])).elim

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@oddEnergy_le_twice_integerEnergy)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.familyRegistration
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
