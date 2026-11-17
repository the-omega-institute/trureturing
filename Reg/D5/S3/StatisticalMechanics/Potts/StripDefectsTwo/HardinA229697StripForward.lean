import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T initial terminal W cl
namespace ForwardCertificate
/- signature: proof_shape=bind-only; consumers=readout,rejected,arena,family,audit -/
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 42) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family,audit -/
def readout : Realization signature := realize signature (fun _ _ s => initial s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law,family -/
def rejected : Realization signature := realize signature (fun _ _ s => initial s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law,family,audit -/
abbrev arena : Arena where
  signature := signature
  Law R :=     (W 0 = (fun s => R.readout () () s) ∧ ∀ i : Fin 17, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 17 = ∑ j : Fin 9, (![216, -1620, 5022, -8343, 8073, -4644, 1557, -288, 27] j : ℤ) • W ⟨8 + j.val, by omega⟩
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h.1.1 0
  have ha := congrFun forward_certificate.1.1 0
  change _ = initial 0 + 1 at hb
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @forward_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change initial 0 ≠ initial 1
    decide +kernel
/- audit: proof_shape=bind-only; consumers=LeanInformationAudit registration extraction -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229697Strip.forward_certificate.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardCertificate

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
