import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case6
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
        (⟨38, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 38
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts6 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 38 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts6) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts6, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts6) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass6.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case6

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case7
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
        (⟨39, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 39
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts7 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 39 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts7) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts7, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts7) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass7.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case7

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case8
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
        (⟨40, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 40
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts8 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 40 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts8) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts8, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts8) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass8.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case8

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case9
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
        (⟨41, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 41
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts9 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 41 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts9) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts9, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts9) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass9.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case9

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case10
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
        (⟨42, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 42
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts10 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 42 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts10) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts10, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts10) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass10.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case10

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case11
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
        (⟨43, by omega⟩ : Fin 68) then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) 43
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ha := transition_counts11 ![0, 1, 0, 1, 0] ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0] 2) 43 + 1 at hb
  linarith

def family : Registration arena (type_of% @transition_counts11) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts11, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts11) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229692StripClass11.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1.Case11
