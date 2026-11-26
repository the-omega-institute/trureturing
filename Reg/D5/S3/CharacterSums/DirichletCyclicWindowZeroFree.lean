import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCyclicWindowZeroFree
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.CharacterSums.DirichletCyclicWindowZeroFree
open _root_.D5.S3.CharacterSums.DirichletCyclicLaplace
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter MeasureTheory
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.CharacterSums.DirichletCyclicWindowZeroFree

namespace Window

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ
    (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x g => g x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {θ δ C : ℝ},
    (0 < δ ∧
      ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 0 < Y ∧
        ∀ x ∈ Icc Y (Y ^ (1 + δ)),
          V.readout () x (gl1CyclicFamily (r := orderOf χ) χ) ≤ C * x ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧
      ∀ j : ℕ, 1 ≤ j → j < orderOf χ → (χ ^ j).LFunction s ≠ 0

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro H
  let ρ := zetaZeroData.zero 0
  have hρ := zetaZeroData_isNontrivial 0
  have hzero : riemannZeta ρ = 0 := hρ.1
  have hρpos : 0 < ρ.re := hρ.2.1
  have hw : 0 < (1 : ℝ) ∧
      ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 0 < Y ∧
        ∀ x ∈ Icc Y (Y ^ (1 + (1 : ℝ))),
          rejected.readout () x (gl1CyclicFamily (r := orderOf
            (1 : DirichletCharacter ℂ 1)) (1 : DirichletCharacter ℂ 1)) ≤
              (0 : ℝ) * x ^ (ρ.re / 2) := by
    refine ⟨zero_lt_one, fun Y₀ => ?_⟩
    exact ⟨max Y₀ 1, le_max_left _ _, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun x hx => by change (0 : ℝ) ≤ 0 * x ^ (ρ.re / 2); simp⟩
  have hfree := @H 1 inferInstance 1 (ρ.re / 2) 1 0 hw ρ (by linarith)
  exact hfree.1 hzero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), ?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

def family : Registration arena (type_of% @gl1_long_window_zero_free) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gl1_long_window_zero_free, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gl1_long_window_zero_free) (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.DirichletCyclicWindowZeroFree.windowUnit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicWindowZeroFree.Window.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x g => g x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicWindowZeroFree
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain",
        "arg", "body", "arg", "body", "arg", "arg", "body",
        "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window



end Reg.D5.S3.CharacterSums.DirichletCyclicWindowZeroFree
