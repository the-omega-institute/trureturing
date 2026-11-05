import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MomentOrthogonalPrimitiveGap
import Reg.Support.SingleDependentReadout

/-! The native complex norm is observed at the primitive energy operand.
The complete original telescope is reconstructed literally. -/

noncomputable section

open _root_.D5.S3.Analytic.MomentOrthogonalPrimitiveGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Set
open scoped Interval

namespace Reg.D5.S3.Analytic.MomentOrthogonalPrimitiveGap

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- All seven original binders, with merely L2, all low moments, arbitrary
complex functions, and the zero function retained. The observation changes
only the literal norm operation in the primitive energy. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (A : ℝ → ℂ)
    (hA : MemLp A 2 (volume.restrict (Icc 0 D)))
    (hm : ∀ r : ℕ, r < q → ∫ x in Icc 0 D, (x : ℂ) ^ r * A x = 0),
    (∫ x in Icc 0 D, (R.readout () () (∫ t in (0 : ℝ)..x, A t)) ^ 2) ≤
      D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
        (∫ x in Icc 0 D, ‖A x‖ ^ 2)

/-- At D=q=1 and A=0 the constant-one observation demands 1≤0. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 1 (by norm_num) 1 (by norm_num) (fun _ => 0)
    MemLp.zero' (by intro r hr; simp)
  norm_num [rejected, realize, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def family : Registration arena (type_of% @complex_L2_moment_primitive_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complex_L2_moment_primitive_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- The primitive energy occurrence selects the native norm function. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complex_L2_moment_primitive_gap) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap.audit
  realizationName := `Reg.D5.S3.Analytic.MomentOrthogonalPrimitiveGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MomentOrthogonalPrimitiveGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.MomentOrthogonalPrimitiveGap
