import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 27) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ s => initial s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ s => initial s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=     (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid (boundary r) (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 27, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = (fun s => R.readout () () s) s) ∧
    (W 0 = (fun s => R.readout () () s) ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-5832, 14580, -13122, 4995, -729, 45] j : ℤ) • W ⟨1 + j.val, by omega⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.2.2.1 0
  have ha := structural_certificate.2.2.2.1 0
  change _ = initial 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @structural_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨structural_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 7, ?_⟩
    change initial 0 ≠ initial 7
    unfold initial
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@structural_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229691StripCertificate.auditUnit
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
  readout := some (realize signature (fun _ _ s => initial s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
