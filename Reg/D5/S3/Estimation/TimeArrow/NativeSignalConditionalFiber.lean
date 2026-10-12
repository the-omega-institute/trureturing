import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open _root_.D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sigmoid x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ a x : ℝ,
    HasDerivAt (fun u : ℝ => Real.sigmoid (u + a))
      (R.readout () () (x + a) * (1 - Real.sigmoid (x + a))) x

private theorem actual_law : arena.Law actual := by
  exact sigmoid_shift_deriv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h 0 0).unique (sigmoid_shift_deriv 0 0)
  norm_num [rejected, realize, Real.sigmoid_zero] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Real.sigmoid 0 ≠ Real.sigmoid 1
    exact fun h => (by norm_num : (0 : ℝ) ≠ 1) (Real.sigmoid_injective h)

noncomputable def registration_1 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv) (Realization signature) Unit Unit := {
  unitName := (Lean.Name.str (Lean.Name.str `D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => Real.sigmoid x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
