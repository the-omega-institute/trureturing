import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
import Reg.Support.SingleDependentReadout

/-! Source readout of right-endpoint cost at a fixed number of bins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ m t => rightEndpointCost t m) (fun e => nomatch e)

private def excessiveCost (cap : ℝ) : Realization signature :=
  realize signature (fun _ _ _ => cap + 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun n => (n : ℝ)), ?_⟩
  change rightEndpointCost (fun _ => 0) 1 ≠ rightEndpointCost (fun n => (n : ℝ)) 1
  norm_num [rightEndpointCost]
  exact ne_of_gt (sigmoid_pos _)

private theorem unit_width (i : ℕ) : ((i + 1 : ℕ) : ℝ) - (i : ℝ) = 1 := by
  push_cast
  ring

namespace Finite

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t : ℕ → ℝ} {m : ℕ} {U δ : ℝ}, 0 < m → t 0 = 0 → t m = U →
    (∀ i < m, 0 < t (i + 1) - t i) → (∀ i < m, t (i + 1) - t i ≤ δ) →
    R.readout () m t ≤
      2 * (∫ u in (0 : ℝ)..U, u * sigmoid (-u)) + 2 * δ * (∫ u in (0 : ℝ)..U, sigmoid (-u)) ∧
    0 ≤ 2 * (∫ u in (0 : ℝ)..U, binEntropy (sigmoid (-u))) - rightEndpointEntropy t m ∧
    2 * (∫ u in (0 : ℝ)..U, binEntropy (sigmoid (-u))) - rightEndpointEntropy t m ≤
      2 * δ * (log 2 - binEntropy (sigmoid (-U))) ∧
    2 * δ * (log 2 - binEntropy (sigmoid (-U))) ≤ 2 * δ * log 2

private def rejected : Realization signature :=
  excessiveCost (2 * (∫ u in (0 : ℝ)..1, u * sigmoid (-u)) +
    2 * (∫ u in (0 : ℝ)..1, sigmoid (-u)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h (t := fun i => (i : ℝ)) (m := 1) (U := 1) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i _ => by rw [unit_width]; norm_num)
    (fun i _ => by rw [unit_width])).1
  dsimp [rejected, excessiveCost, realize] at hc
  linarith

def family : Registration arena (type_of% @rightEndpoint_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rightEndpoint_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rightEndpoint_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid.rightEndpoint_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid.Finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Finite

namespace Explicit

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t : ℕ → ℝ} {m : ℕ} {U δ : ℝ}, 0 < m → t 0 = 0 → t m = U →
    (∀ i < m, 0 < t (i + 1) - t i) → (∀ i < m, t (i + 1) - t i ≤ δ) →
    R.readout () m t ≤ π ^ 2 / 6 + 2 * δ * log 2 ∧
    (2 : ℝ) * (π ^ 2 / 6) - 2 * (U + 2) * exp (-U) - 2 * δ * log 2 ≤
      rightEndpointEntropy t m

private def rejected : Realization signature :=
  excessiveCost (π ^ 2 / 6 + 2 * log 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h (t := fun i => (i : ℝ)) (m := 1) (U := 1) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i _ => by rw [unit_width]; norm_num)
    (fun i _ => by rw [unit_width])).1
  dsimp [rejected, excessiveCost, realize] at hc
  linarith

def family : Registration arena (type_of% @rightEndpoint_explicit_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rightEndpoint_explicit_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rightEndpoint_explicit_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid.rightEndpoint_explicit_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid.Explicit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Explicit

namespace Uniform

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {η ρ : ℝ}, 0 < η → 0 < ρ →
    ∃ (U : ℝ) (m : ℕ),
      1 ≤ U ∧ 0 < m ∧
      R.readout () m (fun i => (i : ℝ) * (U / m)) ≤ (π ^ 2 / 6) * (1 + η / 2) ∧
      (2 : ℝ) * (π ^ 2 / 6) - ρ ≤ rightEndpointEntropy (fun i => (i : ℝ) * (U / m)) m

private def rejected : Realization signature :=
  excessiveCost ((π ^ 2 / 6) * (1 + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, m, _, _, hc, _⟩ := h (η := 2) (ρ := 1) (by norm_num) (by norm_num)
  dsimp [rejected, excessiveCost, realize] at hc
  linarith

def family : Registration arena (type_of% @exists_uniform_rightEndpoint_grid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_uniform_rightEndpoint_grid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_uniform_rightEndpoint_grid) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid.exists_uniform_rightEndpoint_grid.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid.Uniform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
