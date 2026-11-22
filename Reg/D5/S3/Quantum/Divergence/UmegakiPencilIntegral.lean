import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiPencilIntegral

/-! Source-bound audit of the logarithm at the second endpoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open Matrix MeasureTheory RHLinalg
open scoped ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
open _root_.D5.S3.Quantum.Divergence.UmegakiPencilIntegral
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiPencilIntegral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

private def negativeOne : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosDef),
    let hM (t : ℝ) := hA.isHermitian.add
      ((hB.isHermitian.sub hA.isHermitian).smul (IsSelfAdjoint.all t))
    (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart (hM t)))) =
      ENNReal.ofReal ((A * (CFC.log A - cfc (F.readout () ()) B)).trace.re - (A - B).trace.re)

private theorem rejected : ¬ arena.{u}.Law negativeOne := by
  intro h
  let n := ULift.{u} Unit
  have hp : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have hactual := lintegral_weighted_negPart_pencil_eq_umegaki hp.posSemidef hp
  have he := hactual.symm.trans (@h n _ _ 1 1 hp.posSemidef hp)
  change ENNReal.ofReal
      (((1 : Matrix n n ℂ) * (CFC.log 1 - cfc Real.log 1)).trace.re -
        (1 - 1 : Matrix n n ℂ).trace.re)
    = ENNReal.ofReal
      (((1 : Matrix n n ℂ) * (CFC.log 1 - cfc (fun _ : ℝ => (-1 : ℝ)) 1)).trace.re -
        (1 - 1 : Matrix n n ℂ).trace.re) at he
  simp [CFC.log, cfc_apply_one, Matrix.trace_one, n] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def family : Registration arena.{u}
    (type_of% @lintegral_weighted_negPart_pencil_eq_umegaki.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lintegral_weighted_negPart_pencil_eq_umegaki, negativeOne, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeOne rejected
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lintegral_weighted_negPart_pencil_eq_umegaki.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiPencilIntegral.lintegral_weighted_negPart_pencil_eq_umegaki.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiPencilIntegral.family
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
    owner := `D5.S3.Quantum.Divergence.UmegakiPencilIntegral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiPencilIntegral
