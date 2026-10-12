import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open _root_.D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge

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
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_hn : 0 < n),
    (n : ℝ) * Real.log n - n + Real.log n / 2 ≤ R.readout () () (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n / 2 + 1

private theorem actual_law : arena.Law actual := by
  exact log_factorial_envelopes

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h (n := 1) (by norm_num)).1
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change Real.log 1 ≠ Real.log 2
    rw [Real.log_one]
    exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

noncomputable def registration_1 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.log_factorial_envelopes) (Realization signature) Unit Unit := {
  unitName := (Lean.Name.str (Lean.Name.str `D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.log_factorial_envelopes "Reg.D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel/Reg.D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel,
    definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
