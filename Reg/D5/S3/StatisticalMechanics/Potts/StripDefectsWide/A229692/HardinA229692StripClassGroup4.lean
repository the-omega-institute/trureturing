import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case24
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 68) (fun _ => Fin 68) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨56, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 56
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts24 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 56 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts24) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts24, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts24) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass24.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case24

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case25
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 68) (fun _ => Fin 68) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨57, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 57
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts25 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 57 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts25) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts25, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts25) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass25.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case25

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case26
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 68) (fun _ => Fin 68) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨58, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 58
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts26 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 58 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts26) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts26, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts26) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass26.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case26

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case27
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 68) (fun _ => Fin 68) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨59, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 59
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts27 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 59 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts27) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts27, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts27) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass27.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case27

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case28
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 68) (fun _ => Fin 68) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨60, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 60
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts28 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 60 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts28) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts28, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts28) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass28.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case28

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case29
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 68) (fun _ => Fin 68) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Boundary) (d : Fin 3),
    Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    ¬ (d.val ≤ 1 ∧ _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.Valid p d.val) →
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) =
        (⟨61, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 61
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts29 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 61 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts29) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts29, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts29) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass29.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4.Case29
