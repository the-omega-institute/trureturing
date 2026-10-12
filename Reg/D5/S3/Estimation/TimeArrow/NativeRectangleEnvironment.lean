import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open _root_.D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open _root_.D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments

@[reducible] def signature : Signature where
  Params := ℝ × ℝ × ℝ × ℝ
  State _ := Fin 4
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p j => cellCounts p.1 p.2.1 p.2.2.1 p.2.2.2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (N Rm U δ t w : ℝ) (_hN : 0 < N) (_hδ : 0 ≤ δ)
    (_hR : δ * N ≤ Rm) (_hR' : Rm ≤ (1 - δ) * N)
    (_hU : δ * N ≤ U) (_hU' : U ≤ (1 - δ) * N)
    (_ht : |t - U * Rm / N| ≤ w),
    ∀ j, δ ^ 2 * N - w ≤ R.readout () (N, Rm, U, t) j

private theorem actual_law : arena.Law actual := by
  exact central_four_cells_lower

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := h 1 0 0 0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(4, 2, 1, 1), 0, 1, ?_⟩
    change cellCounts 4 2 1 1 0 ≠ cellCounts 4 2 1 1 1
    norm_num [cellCounts]

noncomputable def registration_1 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.central_four_cells_lower) (Realization signature) Unit Unit := {
  unitName := (Lean.Name.str (Lean.Name.str `D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.central_four_cells_lower "Reg.D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment/Reg.D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p j => cellCounts p.1 p.2.1 p.2.2.1 p.2.2.2 j) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment,
    definition := none,
    coordinates := #[0, 1, 2, 4],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 13, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
