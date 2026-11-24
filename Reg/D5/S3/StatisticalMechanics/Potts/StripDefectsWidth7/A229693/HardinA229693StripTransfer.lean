import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
  (Boundary Row horizontal antidiagonal boundary cross)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects literalCount)
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State (Valid)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T

namespace Transition
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 168)
    (fun _ => Fin 168 → ℤ)
def readout : Realization signature := realize signature (fun _ _ i => T i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ i j => T i j + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Boundary) (d : ℕ), ∀ s : Fin 168, Valid p d →
    (∑ q : Row, if cross p q + bondDefects horizontal q q ≤ d ∧
      cl (boundary q) (d - (cross p q + bondDefects horizontal q q)) = s
      then (1 : ℤ) else 0) = r.readout () () (cl p d) s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Boundary := ![0, 1, 0, 1, 0, 1]
  have hp : Valid p 2 := by
    unfold Valid
    decide +kernel
  have hh := h p 2 0 hp
  have ha := transition_counts p 2 0 hp
  change _ = T (cl p 2) 0 + 1 at hh
  linarith

def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h₀ : T 0 0 ≠ T 1 0 := by decide +kernel
    exact h₀ (congrFun h 0)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer.Transition.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => T i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transition

namespace CopiedColumn
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ({j : Fin 96 // (exitRead j).val < 72}) (fun _ => Fin 168)
    (fun _ => ℤ)

def readout : Realization signature :=
  realize signature (fun _ j i => T i (j.val.natAdd 72)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ j i => T i (j.val.natAdd 72) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Fin 96) (h : (exitRead j).val < 72) (i : Fin 168),
    R.readout () ⟨j, h⟩ i = T i ((⟨(exitRead j).val, h⟩ : Fin 72).castAdd 96)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 12 (by decide +kernel) 0
  have ht := copied_column 12 (by decide +kernel) 0
  simp only [rejected, realize] at hf
  linarith

def family : Registration arena (type_of% @copied_column) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨copied_column, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨12, by decide +kernel⟩, 0, 72, ?_⟩
    change T 0 84 ≠ T 72 84
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@copied_column) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer.CopiedColumn.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ j i => T i (j.val.natAdd 72)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CopiedColumn


namespace NewColumn
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 96) (fun _ => Fin 168)
    (fun _ => ℤ)

def readout : Realization signature :=
  realize signature (fun _ j i => T i (j.natAdd 72)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ j i => T i (j.natAdd 72) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j k : Fin 96) (_ : 72 ≤ (exitRead j).val) (_ : exitRead j = exitRead k) (i : Fin 168),
    R.readout () j i = T i (k.natAdd 72)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 1 (by decide +kernel) (by decide +kernel) 0
  have ht := new_column_congr 0 1 (by decide +kernel) (by decide +kernel) 0
  simp only [rejected, realize] at hf
  linarith

def family : Registration arena (type_of% @new_column_congr) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨new_column_congr, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 128, ?_⟩
    change T 0 72 ≠ T 128 72
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@new_column_congr) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer.NewColumn.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ j i => T i (j.natAdd 72)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NewColumn


end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
