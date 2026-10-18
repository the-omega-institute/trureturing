import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.ExpandingNormProduct
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Reg.Support.SingleDependentReadout

/-! Full-statement source registration for the inverse-adjoint norm product bound. -/

namespace Reg.D5.S3.Quantum.Schatten.ExpandingNormProduct

open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.Quantum.Schatten.UINorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (A B : Matrix (Fin n) (Fin n) ℂ)
    (m : ℝ), 0 ≤ m →
    (∀ T : Matrix (Fin n) (Fin n) ℂ, (Tᴴ * T - 1).PosSemidef → m ≤ ν.N (A * T * B)) →
    ∀ W : Matrix (Fin n) (Fin n) ℂ, IsUnit W.det →
      R.readout () () (m ^ 2) (ν.N (A * W * B) * ν.N (A * (W⁻¹)ᴴ * B))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 UnitarilyInvariantNorm.zeroDimNorm 0 0 0 le_rfl (fun _ _ => le_rfl) 1 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @sq_le_product_of_expanding_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sq_le_product_of_expanding_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sq_le_product_of_expanding_lower_bound) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.sq_le_product_of_expanding_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.ExpandingNormProduct.source_registration
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
    owner := `D5.S3.Quantum.Schatten.ExpandingNormProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Schatten.ExpandingNormProduct
