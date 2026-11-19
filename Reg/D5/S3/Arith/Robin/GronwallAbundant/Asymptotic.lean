import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GronwallAbundant.Asymptotic
import Reg.Support.SingleDependentReadout

set_option linter.style.longLine false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.GronwallAbundant.Asymptotic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.GronwallAbundant
open Filter
open scoped Topology

namespace code_cost_eventually
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c C : ℝ, 0 < c → 0 < C →
    ∃ a > 0, ∃ D > 0, ∀ᶠ X : ℝ in atTop,
      codeK X (C * (X * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)))) ≤ codeM X ∧
      R.readout () () (codeCost X (C * (X * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)))))
        (D * (X / Real.log X) * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha, D, hD, hh⟩ := h 1 1 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := hh.exists
  exact hX.2
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.code_cost_eventually) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.code_cost_eventually, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.code_cost_eventually) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Asymptotic.code_cost_eventually.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Asymptotic.code_cost_eventually.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Asymptotic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end code_cost_eventually
end Reg.D5.S3.Arith.Robin.GronwallAbundant.Asymptotic
