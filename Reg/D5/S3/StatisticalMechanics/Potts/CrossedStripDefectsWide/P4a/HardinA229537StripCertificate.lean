import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Sector0
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 4 → Fin 3) (fun _ => Fin 14) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ p j => Q (cls (p 0,p 1,p 2,p 3)) j) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun w a b => (fun _ p j => Q (cls (p 0,p 1,p 2,p 3)) j) w a b + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 4 → Fin 3) (j : Fin 14),
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r = 0 ∧ cls (r 0,r 1,r 2,r 3) = j then (1 : ℤ) else 0) = R.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0,0,0,0] 0
  have ha := zero_counts ![0,0,0,0] 0
  simp only [rejected, realize] at hb
  linarith
def family : Registration arena (type_of% @zero_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zero_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(![0,0,0,0] : Fin 4 → Fin 3), 0, 4, ?_⟩
    change (fun _ p j => Q (cls (p 0,p 1,p 2,p 3)) j) () ![0,0,0,0] 0 ≠ (fun _ p j => Q (cls (p 0,p 1,p 2,p 3)) j) () ![0,0,0,0] 4
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@zero_counts) (Realization signature) Type Unit where
  unitName := `Reg.P4a.Sector0.auditUnit
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
  readout := some (realize signature (fun _ p j => Q (cls (p 0,p 1,p 2,p 3)) j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Sector0

namespace Sector1
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 4 → Fin 3) (fun _ => Fin 14) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ p j => T ((cls (p 0,p 1,p 2,p 3)).castAdd 14) (j.natAdd 14)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun w a b => (fun _ p j => T ((cls (p 0,p 1,p 2,p 3)).castAdd 14) (j.natAdd 14)) w a b + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 4 → Fin 3) (j : Fin 14),
    (∑ r : Fin 4 → Fin 3, if bondDefects between p r = 1 ∧ cls (r 0,r 1,r 2,r 3) = j then (1 : ℤ) else 0) = R.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0,0,0,1] 0
  have ha := one_counts ![0,0,0,1] 0
  simp only [rejected, realize] at hb
  linarith
def family : Registration arena (type_of% @one_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(![0,0,0,1] : Fin 4 → Fin 3), 1, 2, ?_⟩
    change (fun _ p j => T ((cls (p 0,p 1,p 2,p 3)).castAdd 14) (j.natAdd 14)) () ![0,0,0,1] 1 ≠ (fun _ p j => T ((cls (p 0,p 1,p 2,p 3)).castAdd 14) (j.natAdd 14)) () ![0,0,0,1] 2
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@one_counts) (Realization signature) Type Unit where
  unitName := `Reg.P4a.Sector1.auditUnit
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
  readout := some (realize signature (fun _ p j => T ((cls (p 0,p 1,p 2,p 3)).castAdd 14) (j.natAdd 14)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Sector1

namespace CertifiedZeropowers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 22) (fun _ => (Fin 14 → ℤ))
def actual : Realization signature := realize signature (fun _ _ i => Z i) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun w a b => (fun _ _ i => Z i) w a b + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 22, (Q ^ i.val).mulVec (1 : Fin 14 → ℤ) = R.readout () () i
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (zero_powers 0) 0
  simp only [rejected, realize, Pi.add_apply, Pi.one_apply] at hb
  linarith
def family : Registration arena (type_of% @zero_powers) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zero_powers, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Z 0 ≠ Z 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@zero_powers) (Realization signature) Type Unit where
  unitName := `Reg.P4a.CertifiedZeropowers.auditUnit
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
  readout := some (realize signature (fun _ _ i => Z i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CertifiedZeropowers

namespace CertifiedPowers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 22) (fun _ => (Fin 28 → ℤ))
def actual : Realization signature := realize signature (fun _ _ i => W i) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun w a b => (fun _ _ i => W i) w a b + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 22, (T ^ i.val).mulVec terminal = R.readout () () i
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (powers 0) 0
  simp only [rejected, realize, Pi.add_apply, Pi.one_apply] at hb
  linarith
def family : Registration arena (type_of% @powers) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@powers, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change W 0 ≠ W 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@powers) (Realization signature) Type Unit where
  unitName := `Reg.P4a.CertifiedPowers.auditUnit
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
  readout := some (realize signature (fun _ _ i => W i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CertifiedPowers

end
end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripCertificate
