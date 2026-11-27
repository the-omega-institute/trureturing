import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor

/-! Source-equivalence registration for the strict sharp-factor witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker MatrixOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.FilteredChannelConditionalGap (filterAction)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act ratios)
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (C : ℝ) (_hd : 2 ≤ Fintype.card A)
    (_hCD : C < (Fintype.card A : ℝ) ^ 2),
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∃ N : QuantumChannel A (A × A),
        (∀ X, act N X = filterAction (sharpFilter A a) X) ∧
        (∀ (J : Type) (fJ : Fintype J), letI := fJ
          ∀ (L : J → Matrix A (A × A) ℂ) (p : ℝ), 0 ≤ p →
            (∑ j, (L j)ᴴ * L j) ≤
              (1 : Matrix (A × A) (A × A) ℂ) →
            (∀ X : Matrix A A ℂ,
              MatrixMap.of_kraus L L (act N X) = (p : ℂ) • X) →
            p ≤ a) ∧
        R.readout () () (C * a) (sInf (ratios N 1 true)) ∧
        (∀ γ : ℝ, 1 ≤ γ → C * a < sInf (ratios N γ false))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, _, _, N, _, _, hbad, _⟩ :=
    h (A := Fin 2) 0 (by simp) (by norm_num)
  exact hbad

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad := congrFun he 1
  norm_num [actual, realize] at hbad

def family : Registration arena
    (type_of% @sharp_factor_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_factor_witness, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_factor_witness) (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor.sharp_factor_witness.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor
