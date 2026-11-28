import D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The endpoint identity depends on the actual argument of U. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer
open _root_.D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes (psi1)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (_hx : 1 ≤ x),
    psi1 x / x - x / 2 =
      U (R.readout () () x) - (2 / x) * (∫ t in (1 : ℝ)..x, U t) -
        (3 / 2 + Real.eulerMascheroniConstant) / x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1 le_rfl
  norm_num [rejected, realize, U, psi1] at h1
  have hg := Real.one_half_lt_eulerMascheroniConstant
  linarith

def family : Registration arena (type_of% @psi1_div_sub_half_eq_integrated_U) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@psi1_div_sub_half_eq_integrated_U, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@psi1_div_sub_half_eq_integrated_U) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer.psi1_div_sub_half_eq_integrated_U.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer
