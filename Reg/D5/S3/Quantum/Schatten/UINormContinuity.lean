import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.UINormContinuity
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Reg.Support.SingleDependentReadout
import Mathlib.Topology.Order.IntermediateValue

/-! Full-statement registrations for norm continuity and scalar optimization. -/

namespace Reg.D5.S3.Quantum.Schatten.UINormContinuity

open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.Quantum.Schatten.UINorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Continuity

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ → ℝ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Continuous f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (ν : UINorm n), R.readout () n ν.N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 UnitarilyInvariantNorm.zeroDimNorm

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let bad : Matrix (Fin 1) (Fin 1) ℂ → ℝ :=
    fun M => if (M 0 0).re = 0 then 0 else 1
  refine ⟨1, (fun _ => 0), bad, ?_⟩
  intro he
  have hb : Continuous bad := Eq.mp he continuous_const
  have hc : Continuous (fun t : ℝ =>
      (fun _ _ => (t : ℂ) : Matrix (Fin 1) (Fin 1) ℂ)) :=
    continuous_pi fun _ => continuous_pi fun _ => Complex.continuous_ofReal
  have hs : Continuous (fun t : ℝ => if t = 0 then (0 : ℝ) else 1) := hb.comp hc
  have hi := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hs.continuousOn
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc
      ((fun t : ℝ => if t = 0 then (0 : ℝ) else 1) 0)
      ((fun t : ℝ => if t = 0 then (0 : ℝ) else 1) 1) := by norm_num
  obtain ⟨x, _, hx⟩ := hi hhalf
  dsimp only at hx
  split_ifs at hx <;> norm_num at hx

def source_registration : Registration arena (type_of% @continuous_N) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuous_N, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@continuous_N) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.continuous_N.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UINormContinuity.Continuity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Continuous f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.UINormContinuity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Continuity

namespace ScalarOptimization

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (m f g : ℝ), 0 ≤ m → 0 ≤ f → 0 ≤ g →
    (∀ t : ℝ, 0 < t → 2 * m ≤ t * f + t⁻¹ * g) → R.readout () () (m ^ 2) (f * g)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 le_rfl le_rfl le_rfl (by intro t ht; simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @sq_le_mul_of_balanced_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sq_le_mul_of_balanced_bounds, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sq_le_mul_of_balanced_bounds) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.sq_le_mul_of_balanced_bounds.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.UINormContinuity.ScalarOptimization.source_registration
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
    owner := `D5.S3.Quantum.Schatten.UINormContinuity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ScalarOptimization
end
end Reg.D5.S3.Quantum.Schatten.UINormContinuity
