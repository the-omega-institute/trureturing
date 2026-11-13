import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observation families for quantitative defect-spectrum estimates. -/
noncomputable section
open Finset Matrix
open scoped BigOperators
open _root_.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def oneReadout : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

private def sourceFamily (law : Realization signature → Prop) (statement : Prop)
    (bridge : statement ↔ law actual) (good : law actual)
    (bad : Realization signature) (hbad : ¬ law bad) :
    Registration ⟨signature, law⟩ statement where
  actual := actual
  bridge := bridge
  variation := ⟨good, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity law actual bad hbad
  dependence := dependence

namespace ScalarGap
abbrev law (R : Realization signature) : Prop :=
  ∀ {c K lam mu x y z : ℝ}, 0 < c → 0 < K →
    (lam - mu) * z = c * x * y → 1 ≤ K * x ^ 2 → 1 ≤ K * y ^ 2 → |z| ≤ 1 →
      c / K ≤ R.readout () () |lam - mu|
private theorem bad : ¬ law zeroReadout := by
  intro h
  have hh := @h 1 1 1 0 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [zeroReadout, realize, signature, Reg.Support.SingleDependentReadout.signature] at hh

def family : Registration ⟨signature, law⟩ (type_of% @rank_one_gap_from_identity) :=
  sourceFamily law _ Iff.rfl (@rank_one_gap_from_identity) zeroReadout bad
end ScalarGap

namespace ScalarGap
def audit : Contract.Registration (@rank_one_gap_from_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.ScalarGap.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap.ScalarGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨⟨signature, law⟩⟩
  objectArena := .source ⟨⟨signature, law⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨signature, law⟩ ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ScalarGap

end Reg.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
