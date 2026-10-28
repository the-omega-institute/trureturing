import D5.S3.Quantum.Matrix.HsfQubitCubicCertificate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the closed rectangle cubic residual inequality. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate
noncomputable section

/- This is a source-binding attempt. Only the scoped producer's actual
declared-template verdict may certify current binding evidence. -/

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t y : ℝ), 0 ≤ t → 2*t^2 ≤ 1 → 0 ≤ y → y^2 ≤ 2 →
    R.readout () () 0 (J t y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hz : (0 : ℝ) ≤ 0 := le_rfl
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) hz
  norm_num at hf

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate.rectangular_J_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate.rectangular_J_nonneg,
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate.rectangular_J_nonneg)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitCubicCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.HsfQubitCubicCertificate
