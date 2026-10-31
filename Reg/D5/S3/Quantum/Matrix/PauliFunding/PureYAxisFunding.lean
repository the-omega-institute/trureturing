import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.PauliFunding.PureYAxisFunding
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisFunding

open _root_.D5.S3.Quantum.Matrix.PauliFunding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _a : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p t => fundingCoefficient p.1 t p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a y X Y Z : ℝ), 0 ≤ a → a ≤ 1 → y ^ 2 = 1 →
    X ^ 2 + Y ^ 2 + Z ^ 2 = 1 → ∀ j : ℕ, 1 ≤ j →
    let t := (-y * Y) * Real.sqrt (1 - a ^ 2)
    IntegrableOn (complexMoment a t j) (Ioi 0) ∧ 0 ≤ R.readout () ⟨a, j⟩ t ∧
      (0 < fundingCoefficient a t j ↔ a < 1 ∧ |Y| < 1) ∧
      (fundingCoefficient a t j = 0 ↔ a = 1 ∨ |Y| = 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hn := (hh 0 1 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 le_rfl).2.1
  norm_num [rejected, realize] at hn

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 1⟩, 0, -1, ?_⟩
  have hp := (pure_y_axis_funding 0 1 1 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 le_rfl).2.2.1.mpr ⟨by norm_num, by norm_num⟩
  have hz := (pure_y_axis_funding 0 1 0 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 le_rfl).2.2.2.mpr (Or.inr (by norm_num))
  have hp' : 0 < fundingCoefficient 0 0 1 := by simpa using hp
  have hz' : fundingCoefficient 0 (-1) 1 = 0 := by simpa using hz
  intro he
  have he' : fundingCoefficient 0 0 1 = fundingCoefficient 0 (-1) 1 := by
    simpa [actual, realize] using he
  rw [he', hz'] at hp'
  exact (lt_irrefl (0 : ℝ)) hp'

def family : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Matrix.PauliFunding.pure_y_axis_funding)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PauliFunding.pure_y_axis_funding,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.PauliFunding.pure_y_axis_funding)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisFunding.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisFunding.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p t => fundingCoefficient p.1 t p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PauliFunding.PureYAxisFunding
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.PauliFunding.PureYAxisFunding
