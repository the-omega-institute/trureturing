import D5.S3.Quantum.Foundation.TrigonometricMomentGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source reconstruction and actual evaluation on the original infinite
effect/state domain. A whole-family intervention and sensitivity certificate,
observational dependence and a raw source selector remain separate obligations. -/

noncomputable section

namespace Reg.D5.S3.Quantum.Foundation.TrigonometricMomentGap

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.WeightedRelationConfirmation
open _root_.D5.S3.Quantum.Foundation.TrigonometricMomentGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := (Carrier →ₗ[ℝ] ℝ) × Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x.1 x.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O :=
    base cone unit = lift '' body ∧
    pure cone unit = Set.range curve ∧
    (∀ f : Carrier →ₗ[ℝ] ℝ, ∃ a b, f = effect a b) ∧
    (∀ a b, proper cone unit (effect a b) ↔
      ∀ θ : ℝ, 0 ≤ trigonometric a b θ ∧ trigonometric a b θ ≤ 1) ∧
    (∀ w ∈ cone, w ≠ 0 → 0 < unit w) ∧
    p ∈ base cone unit ∧ x ∈ base cone unit ∧ y ∈ base cone unit ∧
    mixed ∈ base cone unit ∧ z ∈ base cone unit ∧
    (∀ f, confirms cone unit p f → (1 / 10 : ℝ) ≤ O.readout () () (f, mixed)) ∧
    confirms cone unit p attainer ∧ O.readout () () (attainer, mixed) = 1 / 10 ∧
    comparison cone unit p mixed = 1 / 10 ∧
    (∃ f, confirms cone unit p f ∧ O.readout () () (f, x) = 0) ∧
    (∃ f, confirms cone unit p f ∧ O.readout () () (f, y) = 0) ∧
    ¬ zeroGluing cone unit

abbrev sourceScope : Prop := type_of% attained_full_effect_gap

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp attained_full_effect_gap

end Reg.D5.S3.Quantum.Foundation.TrigonometricMomentGap
