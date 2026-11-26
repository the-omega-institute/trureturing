import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark

/-! Source-equivalence registrations for the exact conditional and recovery coefficients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion (heraldedRecoveryProbabilities)
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act ratios)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open _root_.FilteredChannelConditionalGap (exists_filtered_channel filterAction)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

namespace Expansion

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A : Type} [Fintype A] [DecidableEq A]
    (a : ℝ) (_ha : 0 < a) (_ha₁ : a < 1) (_hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (_hN : ∀ X, act N X = filterAction (sharpFilter A a) X)
    (γ : ℝ) (_hγ : 1 ≤ γ) (orth : Bool),
    R.readout () () (sInf (ratios N γ orth)) (harmonicParameter (Fintype.card A) a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have ha₁ : (1 / 2 : ℝ) < 1 := by norm_num
  have hd : 2 ≤ Fintype.card (Fin 2) := by simp
  obtain ⟨N, hN⟩ := exists_filtered_channel (sharpFilter (Fin 2) (1 / 2))
    (sharpFilter_posDef (1 / 2) ha ha₁ hd) (sharpFilter_normalized (1 / 2) hd)
  exact h (1 / 2) ha ha₁ hd N hN 1 le_rfl true

def family : Registration arena (type_of% @sharp_family_expansion_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_family_expansion_eq, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_family_expansion_eq) (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark.sharp_family_expansion_eq.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark.Expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Expansion

namespace Recovery

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A : Type} [Fintype A] [DecidableEq A]
    (a : ℝ) (_ha : 0 < a) (_ha₁ : a < 1) (_hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (_hN : ∀ X, act N X = filterAction (sharpFilter A a) X),
    R.readout () () (sSup (heraldedRecoveryProbabilities N)) a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have ha₁ : (1 / 2 : ℝ) < 1 := by norm_num
  have hd : 2 ≤ Fintype.card (Fin 2) := by simp
  obtain ⟨N, hN⟩ := exists_filtered_channel (sharpFilter (Fin 2) (1 / 2))
    (sharpFilter_posDef (1 / 2) ha ha₁ hd) (sharpFilter_normalized (1 / 2) hd)
  exact h (1 / 2) ha ha₁ hd N hN

def family : Registration arena (type_of% @sharp_family_recovery_sup_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_family_recovery_sup_eq, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_family_recovery_sup_eq) (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark.sharp_family_recovery_sup_eq.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark.Recovery.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Recovery

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.DattaHolevoExactBenchmark
