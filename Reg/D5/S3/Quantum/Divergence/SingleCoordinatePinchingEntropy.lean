import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy

/-! Source-bound audits of the logarithm readouts in the determinant integral and pinching bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open Matrix MeasureTheory Set LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy

namespace Reg.D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

private def shiftedLog : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)

private def negativeOne : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

abbrev integralArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htr : X.trace.re = Y.trace.re),
    IntegrableOn (fun s : ℝ => R.readout () () (Y + s • 1).det.re -
      Real.log (X + s • 1).det.re) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), Real.log (Y + s • 1).det.re - Real.log (X + s • 1).det.re) =
      (X * CFC.log X).trace.re - (Y * CFC.log Y).trace.re

private theorem shiftedLog_rejected : ¬ integralArena.{u}.Law shiftedLog := by
  intro h
  have hi := (@h (ULift.{u} Unit) _ _ 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero rfl).1
  change IntegrableOn (fun s : ℝ =>
    Real.log ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) + s • 1).det.re + 1 -
      Real.log ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) + s • 1).det.re) (Ioi 0) at hi
  simp only [add_sub_cancel_left] at hi
  simpa [Real.volume_Ioi] using (integrableOn_const_iff (C := (1 : ℝ))).mp hi

def integralFamily : Registration integralArena.{u} (type_of% @integral_log_det_shift_sub.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_log_det_shift_sub, shiftedLog, shiftedLog_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integralArena.Law actual shiftedLog shiftedLog_rejected
  dependence := dependence

set_option linter.unusedVariables false in
abbrev pinchingArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (C F : Matrix n n ℂ) (h : Matrix n Unit ℂ)
    (a lam c u v : ℝ) (hC : C.PosDef) (hlam : 0 < lam) (hlc : lam < c) (hu : 0 < u)
    (hd : 0 < (v - u) / 2) (hdu : (v - u) / 2 < u)
    (hcap : C ≤ c • (1 : Matrix n n ℂ))
    (hlo : u • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ) ≤
      fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ))
    (hhi : fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ) ≤
      v • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ)),
    let d := (v - u) / 2
    let A := fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ)
    let A₀ := fromBlocks F 0 0 (a • 1 : Matrix Unit Unit ℂ)
    let cost := (A * CFC.log A).trace.re - (A₀ * CFC.log A₀).trace.re
    0 ≤ cost ∧
      cost ≤ (u * d ^ 2 / (u ^ 2 - d ^ 2)) * lam * (c / (c - lam)) * R.readout () () (c / lam)

private theorem negativeOne_rejected : ¬ pinchingArena.{u}.Law negativeOne := by
  intro h
  let n := ULift.{u} Unit
  have hcap : (1 : Matrix n n ℂ) ≤ (2 : ℝ) • 1 :=
    le_smul_of_one_le_left (zero_le_one' _) (by norm_num)
  have hlo : (1 : ℝ) • fromBlocks (1 : Matrix n n ℂ) (0 : Matrix n Unit ℂ) 0
      ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) ≤
      fromBlocks 1 (0 : Matrix n Unit ℂ) (0 : Matrix n Unit ℂ)ᴴ
        ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) := by simp
  have hhi : fromBlocks (1 : Matrix n n ℂ) (0 : Matrix n Unit ℂ) (0 : Matrix n Unit ℂ)ᴴ
      ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) ≤
      (2 : ℝ) • fromBlocks (1 : Matrix n n ℂ) 0 0 ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) := by
    rw [one_smul, conjTranspose_zero, fromBlocks_one]
    exact le_smul_of_one_le_left (zero_le_one' _) (by norm_num)
  have hres := (@h n _ _ 1 1 0 1 1 2 1 2 Matrix.PosDef.one
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcap hlo hhi)
  have hupper := hres.2
  change _ ≤ (1 * ((2 - 1) / 2) ^ 2 / (1 ^ 2 - ((2 - 1) / 2) ^ 2) : ℝ) *
    1 * (2 / (2 - 1)) * (-1) at hupper
  norm_num at hupper

def pinchingFamily :
    Registration pinchingArena.{u} (type_of% @trace_entropy_pinching_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_entropy_pinching_bound, negativeOne, negativeOne_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    pinchingArena.Law actual negativeOne negativeOne_rejected
  dependence := dependence

set_option linter.style.longLine false in
def integralAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_log_det_shift_sub.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy.integral_log_det_shift_sub.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy.integralFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integralArena⟩
  objectArena := .source ⟨integralArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integralArena ⟨integralFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option linter.style.longLine false in
def pinchingAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_entropy_pinching_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy.trace_entropy_pinching_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy.pinchingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pinchingArena⟩
  objectArena := .source ⟨pinchingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pinchingArena ⟨pinchingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body",
        "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy
