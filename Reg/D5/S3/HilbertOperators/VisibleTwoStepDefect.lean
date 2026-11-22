import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HilbertOperators.VisibleTwoStepDefect
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Vary the squared leakage readout by an additive scalar offset.
The zero time step detects a unit offset. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HilbertOperators.VisibleTwoStepDefect
open LeanInformationAudit

namespace Reg.D5.S3.HilbertOperators.VisibleTwoStepDefect
noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)
def shifted : Realization signature :=
  realize signature (fun _ _ x => x ^ 2 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (V : Submodule ℝ E) [V.HasOrthogonalProjection] (T : E →L[ℝ] E)
      (_ : T.toLinearMap.IsSymmetric),
    (∀ v : V, defectForm V T v = R.readout () () ‖T v - V.starProjection (T v)‖) ∧
    ((∀ v : V, defectForm V T v = 0) ↔ ∀ v : V, T v ∈ V)

private theorem shifted_fails : ¬arena.{u}.Law shifted := by
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let V : Submodule ℝ E := ⊤
  have hT : (0 : E →L[ℝ] E).toLinearMap.IsSymmetric := by intro x y; simp
  have eq := (law V 0 hT).1 0
  change defectForm V 0 0 = _ ^ 2 + 1 at eq
  simp [defectForm] at eq

def family : Registration arena.{u} (type_of% @visible_two_step_defect.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@visible_two_step_defect, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) ^ (2 : ℕ) ≠ 1 ^ (2 : ℕ)
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow] using (zero_ne_one : (0 : ℝ) ≠ 1)

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.HilbertOperators.VisibleTwoStepDefect.visible_two_step_defect.{u})
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.VisibleTwoStepDefect.unit
  realizationName := `Reg.D5.S3.HilbertOperators.VisibleTwoStepDefect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.VisibleTwoStepDefect
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.HilbertOperators.VisibleTwoStepDefect
