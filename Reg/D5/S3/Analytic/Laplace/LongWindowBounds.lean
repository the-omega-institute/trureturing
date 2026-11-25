import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.LongWindowBounds
import Reg.Support.SingleDependentReadout

/-! Source-equivalent readouts with explicit variation and observational dependence. -/

open _root_.D5.S3.Analytic.Laplace.LongWindowBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Analytic.Laplace.LongWindowBounds

namespace Growth
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def arena : Arena where
  signature := signature
  Law V := ∀ {c d e C : ℝ}, 0 < c → 0 < d → d < e →
    let η := Real.log (e / d) / 2
    let U₀ := 2 * |C| / (c * Real.log (e / d))
    0 < η ∧ 0 ≤ U₀ ∧ ∀ U ≥ U₀, ∀ k : ℕ, U ≤ k →
      C * Real.exp (η * U) / e ^ k < V.readout () () c / d ^ k
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, hb⟩ := @h 1 1 2 0 (by norm_num) (by norm_num) (by norm_num)
  have bad := hb 0 (by norm_num) 0 (by norm_num)
  norm_num [rejected, realize] at bad

def family : Registration arena (type_of% @landau_growth_contra) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@landau_growth_contra, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@landau_growth_contra) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Analytic.Laplace.LongWindowBounds.landau_growth_contra
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Laplace.LongWindowBounds.Growth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.LongWindowBounds
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Growth

namespace Window
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def arena : Arena where
  signature := signature
  Law V := ∀ {c d e E M C : ℝ}, 0 < c → 0 < d → d < e → d < E →
    (∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∃ k : ℕ, U ≤ k ∧
        V.readout () () c / d ^ k ≤ M / e ^ k + C * Real.exp (η * U) / E ^ k) → False
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  apply @h 1 1 2 2 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro η hη U₀
  refine ⟨U₀, le_rfl, ⌈U₀⌉₊, Nat.le_ceil U₀, ?_⟩
  simp [rejected, realize]

def family : Registration arena (type_of% @landau_window_contra) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@landau_window_contra, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@landau_window_contra) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Analytic.Laplace.LongWindowBounds.landau_window_contra
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Laplace.LongWindowBounds.Window.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.LongWindowBounds
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "fn",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Window

end Reg.D5.S3.Analytic.Laplace.LongWindowBounds
