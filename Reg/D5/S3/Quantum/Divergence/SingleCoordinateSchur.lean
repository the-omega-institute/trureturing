import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.SingleCoordinateSchur

/-! Source-bound audit of the logarithm of the pinched determinant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.SingleCoordinateSchur

namespace Reg.D5.S3.Quantum.Divergence.SingleCoordinateSchur

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

private def negativeOne : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C F : Matrix ι ι ℂ) (h : Matrix ι Unit ℂ)
    (a lam c u v s : ℝ) (hC : C.PosDef) (hlam : 0 < lam) (hc : 0 < c) (hu : 0 < u)
    (hd : 0 < (v - u) / 2) (hdu : (v - u) / 2 < u) (hs : 0 ≤ s)
    (hcap : C ≤ c • (1 : Matrix ι ι ℂ))
    (hlo : u • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ) ≤
      fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ))
    (hhi : fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ) ≤
      v • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ)),
    let d := (v - u) / 2
    let A := fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ)
    let A₀ := fromBlocks F 0 0 (a • 1 : Matrix Unit Unit ℂ)
    let q := (hᴴ * (F + s • 1)⁻¹ * h) () () |>.re
    0 ≤ q ∧ q ≤ d ^ 2 * lam * c / (u * c + s) ∧
    (A + s • 1).det.re / (A₀ + s • 1).det.re = 1 - q / (a + s) ∧
    0 ≤ q / (a + s) ∧ q / (a + s) ≤ d ^ 2 * lam * c / ((u * c + s) * (u * lam + s)) ∧
    d ^ 2 * lam * c / ((u * c + s) * (u * lam + s)) ≤ d ^ 2 / u ^ 2 ∧
    0 ≤ R.readout () () (A₀ + s • 1).det.re - Real.log (A + s • 1).det.re ∧
    Real.log (A₀ + s • 1).det.re - Real.log (A + s • 1).det.re ≤
      (d ^ 2 * lam * c / ((u * c + s) * (u * lam + s))) / (1 - d ^ 2 / u ^ 2)

private theorem rejected : ¬ arena.{u}.Law negativeOne := by
  intro h
  let ι := ULift.{u} Unit
  have hId : fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι Unit ℂ)
      (0 : Matrix Unit ι ℂ) (1 : Matrix Unit Unit ℂ) = 1 := fromBlocks_one
  have hlo : (1 : ℝ) • fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι Unit ℂ) 0
      ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) ≤
      fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι Unit ℂ) (0 : Matrix ι Unit ℂ)ᴴ
        ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) := by simp
  have hhi : fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι Unit ℂ) (0 : Matrix ι Unit ℂ)ᴴ
        ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) ≤
      (2 : ℝ) • fromBlocks (1 : Matrix ι ι ℂ) 0 0 ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) := by
    rw [one_smul, conjTranspose_zero, hId]
    exact le_smul_of_one_le_left (zero_le_one' (Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)) (by norm_num)
  have hresult := @h ι _ _ 1 1 0 1 1 1 1 2 0 Matrix.PosDef.one (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by simp) hlo hhi
  have hlog := hresult.2.2.2.2.2.2.1
  change 0 ≤ (-1 : ℝ) -
    Real.log (fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι Unit ℂ) (0 : Matrix ι Unit ℂ)ᴴ
      ((1 : ℝ) • (1 : Matrix Unit Unit ℂ)) + (0 : ℝ) • 1).det.re at hlog
  rw [one_smul, conjTranspose_zero, hId, zero_smul, add_zero, Matrix.det_one,
    Complex.one_re, Real.log_one, sub_zero] at hlog
  norm_num at hlog

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def family : Registration arena.{u} (type_of% @schur_det_log_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@schur_det_log_bound, negativeOne, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeOne rejected
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@schur_det_log_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SingleCoordinateSchur.schur_det_log_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SingleCoordinateSchur.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.SingleCoordinateSchur
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.SingleCoordinateSchur
