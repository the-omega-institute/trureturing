import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GronwallAbundant.Upper
import Reg.Support.SingleDependentReadout

set_option linter.style.longLine false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.GronwallAbundant.Upper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.GronwallAbundant
open Filter
open scoped Topology

namespace ga1_log_count_le_cost
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X B : ℝ}, 2 ≤ X → codeK X B ≤ codeM X →
    (∀ N : ℕ, IsProperGA1 N → Real.log N ≤ X → missingMass N (primeEnd N) ≤ B) →
    R.readout () () (Real.log (1 + (Q1 (Real.exp X) : ℝ))) (codeCost X B)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (X := 2) (B := 0) le_rfl (by norm_num [codeK, codeM]) (by
    intro N hN hNX
    exact False.elim ((not_le.mpr (proper_log_gt_two hN)) hNX))
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_log_count_le_cost) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_log_count_le_cost, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_log_count_le_cost) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Upper.ga1_log_count_le_cost.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Upper.ga1_log_count_le_cost.source_registration
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
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ga1_log_count_le_cost

namespace result
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∃ a > 0, ∃ C > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
    R.readout () () (Real.log (1 + (Q1 x : ℝ)))
      (C * (Real.log x / Real.log (Real.log x)) *
        Real.exp (-a * (Real.log (Real.log x)) ^ ((1 : ℝ) / 10)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha, C, hC, x₀, hh⟩ := h
  exact hh x₀ le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Upper.result.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Upper.result.source_registration
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
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "arg", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end result
end Reg.D5.S3.Arith.Robin.GronwallAbundant.Upper
