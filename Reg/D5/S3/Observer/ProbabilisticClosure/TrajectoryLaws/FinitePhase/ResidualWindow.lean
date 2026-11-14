import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
import Reg.Support.DependentFamily

/-! Complete source families for the two complex-modulus observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

namespace Core

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : Matrix I I ℝ), P ∈ Matrix.rowStochastic ℝ I →
    ∀ (w : ℂ), ‖w‖ = 1 → ∀ (v : I → ℂ), v ≠ 0 →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ Fintype.card I ∧
      (R.readout () () (1-w^r))^2 * ‖v‖ ≤
        8 * (Fintype.card I : ℝ) * ‖v - w • (complexMatrix P *ᵥ v)‖

private theorem actual_law : arena.{u}.Law actual := @phase_residual.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let X := ULift.{u} Unit
  have hv : (fun _ : X => (1:ℂ)) ≠ 0 := by
    intro he
    have := congrFun he (ULift.up ())
    norm_num at this
  have ht := h (1 : Matrix X X ℝ) (Matrix.rowStochastic ℝ X).one_mem
    1 (by norm_num) (fun _ => 1) hv
  norm_num [rejected, realize, complexMatrix] at ht

def evidence : Registration arena.{u} (type_of% (@phase_residual.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun _ => ⟨rejected,
    fun _ h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phase_residual.{u})
    (type_of% (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))) Unit Unit where
  unitName := `ResidualWindow.phase_residual.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow.Core.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Core

namespace Window

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : Matrix I I ℝ), P ∈ Matrix.rowStochastic ℝ I →
    ∀ (z : ℂ), ‖z‖ = 1 → ∀ (j : ℤ), j ≠ 0 →
    ∀ (γ : ℝ), 0 < γ →
    (∀ r : ℕ, 1 ≤ r → r ≤ Fintype.card I → γ ≤ ‖1-z^(j*(r:ℤ))‖) →
    ∀ (α b : I → ℝ), (∀ i, 0 ≤ α i) → (∑ i, α i = 1) →
    (∀ i, 0 ≤ b i ∧ b i ≤ 1) → ∀ (m N : ℕ), 0 < N →
    R.readout () () (phaseWindow P α b z j m N) ≤
      16 * (Fintype.card I : ℝ) / ((N : ℝ)*γ^2)

private theorem actual_law : arena.{u}.Law actual := @window_average.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let X := ULift.{u} Unit
  have hgap : ∀ r : ℕ, 1 ≤ r → r ≤ Fintype.card X →
      (1:ℝ) ≤ ‖1-(-1:ℂ)^((1:ℤ)*(r:ℤ))‖ := by
    intro r hr hS
    have he : r = 1 := by simpa [X] using Nat.le_antisymm hS hr
    subst r
    norm_num
  have hh := h (1 : Matrix X X ℝ) (Matrix.rowStochastic ℝ X).one_mem
    (-1) (by norm_num) 1 (by norm_num) 1 (by norm_num) hgap
    (fun _ => 1) (fun _ => 0) (by norm_num)
    (by simp [X]) (by norm_num) 0 17 (by norm_num)
  norm_num [rejected, realize, X] at hh

def evidence : Registration arena.{u} (type_of% (@window_average.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun _ => ⟨rejected,
    fun _ h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@window_average.{u})
    (type_of% (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))) Unit Unit where
  unitName := `ResidualWindow.window_average.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow.Window.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Window

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase.ResidualWindow
