import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.PositiveReferenceReplacement

/-! A source-bound audit of the logarithm of the reference scaling factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.PositiveReferenceReplacement
open private D from D5.S3.Quantum.Divergence.PositiveReferenceReplacement

namespace Reg.D5.S3.Quantum.Divergence.PositiveReferenceReplacement

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

private def shiftedLog : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)

set_option linter.unusedVariables false in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n] (C F : Matrix n n ℂ)
    (lam u a : ℝ) (hC : C.PosDef) (hlam : 0 < lam) (hu : 0 < u) (ha : 0 < a)
    (hlo : u • C ≤ F),
    let b := C.trace.re
    let c := b + lam
    let τ := b⁻¹ • C
    let F' := F + a • τ
    let C' := c • τ
    let t := F.trace.re + a
    let K := D F' F - a
    let E := (τ * (CFC.log F - CFC.log (u • C))).trace.re
    let bound := a * (Real.log (a / (lam * u)) - 1) + t * R.readout () () (c / b)
    D F C + a * Real.log (a / lam) - D F' C' = bound - K - a * E ∧
      ((a • τ)ᴴ * (a • τ)).trace.re / (2 * t) ≤ K ∧ 0 ≤ E ∧
      D F C + a * Real.log (a / lam) - D F' C' ≤
        bound - ((a • τ)ᴴ * (a • τ)).trace.re / (2 * t)

private theorem shiftedLog_rejected : ¬ arena.{u}.Law shiftedLog := by
  intro h
  let n := ULift.{u} Unit
  let X : Matrix n n ℂ := 1
  have hX : X.PosDef := Matrix.PosDef.one
  have hlo : (1 : ℝ) • X ≤ X := by rw [one_smul]
  have hactual := (positive_reference_replacement X X 1 1 1 hX
    zero_lt_one zero_lt_one zero_lt_one hlo).1
  have hshift := (@h n _ _ _ X X 1 1 1 hX zero_lt_one zero_lt_one zero_lt_one hlo).1
  have ht : 0 < X.trace.re + 1 :=
    add_pos (Complex.pos_iff.mp hX.trace_pos).1 zero_lt_one
  dsimp only [shiftedLog, realize] at hshift
  linarith only [hactual, hshift, ht]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def family : Registration arena.{u} (type_of% @positive_reference_replacement.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_reference_replacement, shiftedLog, shiftedLog_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shiftedLog shiftedLog_rejected
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_reference_replacement.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.PositiveReferenceReplacement.positive_reference_replacement.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.PositiveReferenceReplacement.family
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
    owner := `D5.S3.Quantum.Divergence.PositiveReferenceReplacement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.PositiveReferenceReplacement
