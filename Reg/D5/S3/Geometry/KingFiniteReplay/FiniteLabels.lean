import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.KingFiniteReplay.FiniteLabels

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.KingFiniteReplay
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Geometry.KingFiniteReplay.FiniteLabels

abbrev signature : Signature where
  Params := List (ℕ × ℕ) × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => rowBits p.1 x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (E : List (ℕ × ℕ)) (x y : ℕ),
    (R.readout () (E, y) x).testBit y = true ↔ ((x, y) ∈ E ∨ (y, x) ∈ E)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h [(0, 1)] 0 1
  change (0 : ℕ).testBit 1 = true ↔ _ at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨([(0, 1)], 1), 0, 2, ?_⟩
  change rowBits [(0, 1)] 0 ≠ rowBits [(0, 1)] 2
  decide

def family : Registration arena (type_of% rowBits_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rowBits_spec, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim (α := Unit) other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

def rowBitsRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    rowBits_spec (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.KingFiniteReplay.rowBits_spec.__information_unit
  realizationName := `Reg.D5.S3.Geometry.KingFiniteReplay.FiniteLabels.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => rowBits p.1 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.KingFiniteReplay.FiniteLabels
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.KingFiniteReplay.FiniteLabels
