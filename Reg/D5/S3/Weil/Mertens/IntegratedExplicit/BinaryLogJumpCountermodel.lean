import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel
import Reg.Support.SingleDependentReadout

/-! Source audit for the signed mass tolerance of the binary count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    ∃ (c : ℕ → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, c n = 0 ∨ c n = 1) ∧
      (∀ n ≤ 8, c n = 0) ∧
      (∀ n : ℕ, logCount c ((n + 1 : ℕ) : ℝ) - logCount c (n : ℝ) =
        Real.log ((n + 1 : ℕ) : ℝ) * c (n + 1)) ∧
      (∀ x : ℝ, 8 ≤ x → |logCount c x - count x| ≤ |count 8| + 4 * Real.log x ∧
        IntegrableOn (roundedTailKernel c) (Ioi x)) ∧
      Tendsto (fun x : ℝ => logCount c x / x) atTop (𝓝 1) ∧
      (∀ A B : ℝ, 8 ≤ A → A ≤ B →
        |roundedSignedMass c A B + 2 * Real.log (B / A)| ≤ V.readout () () C ∧
        (3 / 2 : ℝ) * (B ^ (1 / 6 : ℝ) - A ^ (1 / 6 : ℝ)) - C ≤ roundedNegativeMass c A B) ∧
      (∀ b : ℝ, 1 < b → ∀ᶠ Y : ℝ in atTop,
        (1 / 4 : ℝ) * Y ^ (b / 6) ≤ roundedNegativeMass c Y (Y ^ b))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro law
  obtain ⟨c, C, -, -, -, -, -, -, hwindow, -⟩ := law
  have hbound := (hwindow 8 8 le_rfl le_rfl).1
  change |roundedSignedMass c 8 8 + 2 * Real.log (8 / 8)| ≤ (-1 : ℝ) at hbound
  linarith only [hbound, abs_nonneg (roundedSignedMass c 8 8 + 2 * Real.log (8 / 8))]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change ((0 : ℝ)) ≠ ((1 : ℝ))
  norm_num

def family : Registration arena (type_of% @roundedWindowObstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@roundedWindowObstruction, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@roundedWindowObstruction) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel.roundedWindowObstruction.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "arg", "fn", "arg", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.BinaryLogJumpCountermodel
